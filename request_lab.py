#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
request_lab.py — 用 requests 练习 HTTP 的本地回显服务器

功能：
  1. 同时启动 HTTP 和 HTTPS 服务；
  2. 原样回显收到的请求行、请求头（含重复头）、Cookie、Authorization、查询参数和请求体；
  3. 提供 /proxy 接口，服务器内部用 requests 发请求，展示 requests 实际发送的请求头；
  4. 提供状态码、重定向、延迟、Basic Auth、Cookie 等练习接口；
  5. 支持 --demo 自检，自动用 requests 跑一遍全部功能。

依赖：pip install requests
运行：python3 request_lab.py
HTTPS 使用自动生成的自签名证书，练习 requests 时用 verify=False。
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import hmac
import json
import os
import re
import ssl
import subprocess
import sys
import threading
import time
import warnings
from collections import defaultdict
from datetime import datetime, timezone
from email.message import Message
from email.parser import BytesParser
from email.policy import default as EMAIL_POLICY
from http import HTTPStatus
from http.cookies import CookieError, SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from typing import Any
from urllib.parse import parse_qs, unquote, urlsplit

import requests


VERSION = "1.0"
MAX_BODY = 2 * 1024 * 1024          # 最多读取 2 MiB 请求体
BODY_TEXT_PREVIEW = 64 * 1024       # JSON 中最多展示 64 KiB 文本
PROXY_PREVIEW = 64 * 1024           # /proxy 最多展示 64 KiB 响应
SCRIPT_DIR = Path(__file__).resolve().parent


# ---------------------------------------------------------------------------
# 原样记录进入服务器的 HTTP 字节
# ---------------------------------------------------------------------------


class _RecordingReader:
    """包装 rfile，把 BaseHTTPRequestHandler 读到的原始字节记录下来。"""

    def __init__(self, rfile: Any, recorded: bytearray) -> None:
        self._rfile = rfile
        self._recorded = recorded

    def readline(self, *args: Any) -> bytes:
        data = self._rfile.readline(*args)
        self._recorded.extend(data)
        return data

    def read(self, *args: Any) -> bytes:
        data = self._rfile.read(*args)
        self._recorded.extend(data)
        return data

    def __getattr__(self, name: str) -> Any:
        return getattr(self._rfile, name)


# ---------------------------------------------------------------------------
# 请求处理
# ---------------------------------------------------------------------------


class LabHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = f"RequestLab/{VERSION}"
    sys_version = ""
    timeout = 30

    # ----- 生命周期 --------------------------------------------------------

    def setup(self) -> None:
        super().setup()
        self._recorded = bytearray()
        self._response_started = False
        self.rfile = _RecordingReader(self.rfile, self._recorded)

    def handle_one_request(self) -> None:
        # 每个 keep-alive 请求单独记录，避免把上一个请求算进来。
        if hasattr(self, "_recorded"):
            self._recorded.clear()
        super().handle_one_request()

    def log_message(self, fmt: str, *args: Any) -> None:
        stamp = datetime.now().strftime("%H:%M:%S")
        print(f"[{stamp}] {self.client_address[0]} {fmt % args}", flush=True)

    # ----- 基础发送 --------------------------------------------------------

    def _send(
        self,
        status: int,
        body: bytes = b"",
        content_type: str | None = None,
        headers: dict[str, str] | None = None,
    ) -> None:
        self._response_started = True
        self.send_response(status)
        if content_type:
            self.send_header("Content-Type", content_type)
        if status not in (204, 304):
            self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Request-Lab", VERSION)
        for name, value in (headers or {}).items():
            self.send_header(name, value)
        if self.close_connection:
            self.send_header("Connection", "close")
        self.end_headers()

        if self.command == "HEAD" or status in (204, 304) or not body:
            return
        try:
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _send_json(self, payload: Any, status: int = 200,
                   headers: dict[str, str] | None = None) -> None:
        body = json.dumps(payload, ensure_ascii=False, indent=2,
                          default=str).encode("utf-8")
        self._send(status, body, "application/json; charset=utf-8", headers)

    def _send_text(self, text: str, status: int = 200,
                   content_type: str = "text/plain; charset=utf-8") -> None:
        self._send(status, text.encode("utf-8"), content_type)

    # ----- 读取请求体 ------------------------------------------------------

    def _read_exact(self, n: int) -> bytes:
        chunks: list[bytes] = []
        remaining = n
        while remaining > 0:
            chunk = self.rfile.read(min(65536, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        return b"".join(chunks)

    def _read_chunked(self) -> tuple[bytes, bool]:
        chunks: list[bytes] = []
        stored = 0
        truncated = False

        while True:
            line = self.rfile.readline(65537)
            if not line:
                raise ValueError("chunked 请求体在块大小前意外结束")
            token = line.split(b";", 1)[0].strip()
            try:
                size = int(token, 16)
            except ValueError as exc:
                raise ValueError(f"无效的 chunk 大小: {token!r}") from exc

            if size == 0:
                # 读取 trailer，直到空行。
                for _ in range(100):
                    trailer = self.rfile.readline(65537)
                    if trailer in (b"\r\n", b"\n", b""):
                        break
                break

            if stored + size > MAX_BODY:
                truncated = True
                self.close_connection = True
                break

            data = self._read_exact(size)
            chunks.append(data)
            stored += len(data)

            ending = self._read_exact(2)
            if ending not in (b"\r\n", b"\n"):
                raise ValueError("chunk 数据后缺少 CRLF")

        return b"".join(chunks), truncated

    def _read_body(self) -> tuple[bytes, bool, int | None]:
        transfer_encoding = self.headers.get("Transfer-Encoding", "")
        if "chunked" in transfer_encoding.lower():
            body, truncated = self._read_chunked()
            return body, truncated, None

        raw_length = self.headers.get("Content-Length")
        if not raw_length:
            return b"", False, None
        try:
            declared = int(raw_length)
        except ValueError as exc:
            raise ValueError(f"无效的 Content-Length: {raw_length!r}") from exc
        if declared < 0:
            raise ValueError(f"无效的 Content-Length: {declared}")
        if declared == 0:
            return b"", False, 0

        body = self._read_exact(min(declared, MAX_BODY))
        truncated = declared > MAX_BODY
        if truncated:
            self.close_connection = True
        return body, truncated, declared

    # ----- 解析辅助 --------------------------------------------------------

    @staticmethod
    def _decode_text(data: bytes, content_type: str | None) -> tuple[str | None, str | None]:
        if not data or b"\x00" in data:
            return None, None

        charset = None
        if content_type:
            message = Message()
            message["content-type"] = content_type
            charset = message.get_content_charset()

        encodings = [charset, "utf-8", "gb18030"]
        for encoding in encodings:
            if not encoding:
                continue
            try:
                return data.decode(encoding), encoding
            except (LookupError, UnicodeDecodeError):
                continue

        # 最后才尝试 latin-1；二进制内容通常会在上面的 UTF-8 校验中失败，
        # 这里再用控制字符检查避免把二进制误标成文本。
        text = data.decode("latin-1")
        controls = sum(1 for ch in text if ord(ch) < 32 and ch not in "\r\n\t")
        if controls / max(len(text), 1) > 0.02:
            return None, None
        return text, "latin-1"

    @staticmethod
    def _parse_multipart(content_type: str, body: bytes) -> dict[str, Any]:
        message = BytesParser(policy=EMAIL_POLICY).parsebytes(
            b"Content-Type: " + content_type.encode("latin-1", "replace")
            + b"\r\nMIME-Version: 1.0\r\n\r\n" + body
        )
        fields: dict[str, list[str]] = defaultdict(list)
        files: list[dict[str, Any]] = []

        if not message.is_multipart():
            return {"fields": {}, "files": []}

        for part in message.iter_parts():
            name = part.get_param("name", header="content-disposition")
            filename = part.get_filename()
            payload = part.get_payload(decode=True) or b""
            part_type = part.get_content_type()

            if filename is not None:
                item: dict[str, Any] = {
                    "field": name,
                    "filename": filename,
                    "content_type": part_type,
                    "size": len(payload),
                    "sha256": hashlib.sha256(payload).hexdigest(),
                }
                preview, encoding = LabHandler._decode_text(payload, part_type)
                if preview is not None:
                    item["text_preview"] = preview[:4096]
                    item["text_encoding"] = encoding
                    item["text_truncated"] = len(preview) > 4096
                files.append(item)
            elif name:
                text, encoding = LabHandler._decode_text(payload, part_type)
                value = text if text is not None else base64.b64encode(payload).decode("ascii")
                fields[name].append(value[:4096])
                if text is not None and len(text) > 4096:
                    fields[name][-1] += "…(截断)"

        return {"fields": dict(fields), "files": files}

    def _body_info(self, body: bytes, truncated: bool,
                   declared: int | None) -> dict[str, Any]:
        content_type = self.headers.get("Content-Type")
        info: dict[str, Any] = {
            "content_type": content_type,
            "declared_length": declared,
            "received_length": len(body),
            "truncated": truncated,
            "sha256": hashlib.sha256(body).hexdigest(),
        }
        if not body:
            return info

        text, encoding = self._decode_text(body, content_type)
        if text is not None:
            info["text"] = text[:BODY_TEXT_PREVIEW]
            info["text_encoding"] = encoding
            info["text_truncated"] = len(text) > BODY_TEXT_PREVIEW
        else:
            info["base64_preview"] = base64.b64encode(body[:4096]).decode("ascii")
            info["base64_preview_truncated"] = len(body) > 4096

        lower_type = (content_type or "").lower()
        if text is not None and "json" in lower_type:
            try:
                info["json"] = json.loads(text)
            except (json.JSONDecodeError, ValueError):
                info["json_error"] = "Content-Type 声明为 JSON，但请求体不是合法 JSON"

        if text is not None and "application/x-www-form-urlencoded" in lower_type:
            info["form"] = parse_qs(text, keep_blank_values=True)

        if "multipart/form-data" in lower_type and not truncated:
            try:
                info["multipart"] = self._parse_multipart(content_type or "", body)
            except Exception as exc:  # multipart 解析失败不应影响回显
                info["multipart_error"] = f"{type(exc).__name__}: {exc}"

        return info

    def _tls_info(self) -> dict[str, Any]:
        if not isinstance(self.connection, ssl.SSLSocket):
            return {"enabled": False}
        cipher = self.connection.cipher()
        try:
            peer_cert = self.connection.getpeercert()
        except ValueError:
            peer_cert = None
        return {
            "enabled": True,
            "version": self.connection.version(),
            "cipher": cipher[0] if cipher else None,
            "cipher_bits": cipher[2] if cipher else None,
            "alpn": self.connection.selected_alpn_protocol(),
            "client_certificate_present": bool(peer_cert),
            "note": "TLS 已在服务器端解密，以下是解密后的 HTTP 请求头。",
        }

    def _raw_head(self) -> bytes:
        raw = bytes(self._recorded)
        index = raw.find(b"\r\n\r\n")
        if index >= 0:
            return raw[:index + 4]
        index = raw.find(b"\n\n")
        if index >= 0:
            return raw[:index + 2]
        return raw

    def _request_headers(self) -> list[dict[str, str]]:
        return [{"name": name, "value": value}
                for name, value in self.headers.items()]

    def _cookies(self) -> dict[str, str]:
        cookies: dict[str, str] = {}
        for raw in self.headers.get_all("Cookie") or []:
            jar = SimpleCookie()
            try:
                jar.load(raw)
            except CookieError:
                continue
            for name, morsel in jar.items():
                cookies[name] = morsel.value
        return cookies

    def _authorization(self) -> dict[str, Any] | None:
        raw = self.headers.get("Authorization")
        if not raw:
            return None

        result: dict[str, Any] = {"raw": raw}
        scheme, _, credentials = raw.partition(" ")
        if scheme.lower() == "basic":
            result["scheme"] = "Basic"
            try:
                decoded = base64.b64decode(credentials, validate=True).decode("utf-8")
                username, _, password = decoded.partition(":")
                result["username"] = username
                result["password"] = password
            except (ValueError, UnicodeDecodeError):
                result["decode_error"] = "Basic 凭据不是合法的 base64/UTF-8"
        elif scheme.lower() == "bearer":
            result["scheme"] = "Bearer"
            result["token"] = credentials
        else:
            result["scheme"] = scheme or None
        return result

    def _scheme(self) -> str:
        return "https" if isinstance(self.connection, ssl.SSLSocket) else "http"

    def _echo_payload(self, path: str, query: dict[str, list[str]],
                      body: bytes, truncated: bool,
                      declared: int | None) -> dict[str, Any]:
        headers = self._request_headers()
        headers_by_name: dict[str, list[str]] = defaultdict(list)
        for item in headers:
            headers_by_name[item["name"].lower()].append(item["value"])

        host = self.headers.get("Host")
        if not host:
            host = f"{self.server.server_address[0]}:{self.server.server_port}"
        url = f"{self._scheme()}://{host}{self.path}"
        tls = self._tls_info()

        return {
            "request_line": self.requestline,
            "method": self.command,
            "url": url,
            "scheme": self._scheme(),
            "protocol": self.request_version,
            "path": path,
            "raw_path": self.path,
            "query_string": urlsplit(self.path).query,
            "query": query,
            "headers": headers,
            "headers_by_name": dict(headers_by_name),
            "headers_count": len(headers),
            "cookie": self._cookies(),
            "cookie_raw": self.headers.get_all("Cookie") or [],
            "authorization": self._authorization(),
            "body": self._body_info(body, truncated, declared),
            "raw_head": self._raw_head().decode("latin-1"),
            "raw_head_bytes": len(self._raw_head()),
            "client": {
                "address": self.client_address[0],
                "port": self.client_address[1],
            },
            "server": {
                "host": self.server.server_address[0],
                "port": self.server.server_port,
            },
            "tls": tls,
            "timestamp": datetime.now(timezone.utc).isoformat(),
        }

    # ----- 路由 ------------------------------------------------------------

    def _dispatch(self) -> None:
        try:
            self._handle()
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as exc:  # 防止单个坏请求打断整个服务
            self.log_error("处理请求失败: %s: %s", type(exc).__name__, exc)
            if not self._response_started:
                self._send_json(
                    {"ok": False, "error": type(exc).__name__, "message": str(exc)},
                    status=500,
                )

    def _handle(self) -> None:
        parsed = urlsplit(self.path)
        path = unquote(parsed.path) or "/"
        query = parse_qs(parsed.query, keep_blank_values=True)

        try:
            body, truncated, declared = self._read_body()
        except ValueError as exc:
            self._send_json({"ok": False, "error": "invalid_request_body",
                             "message": str(exc)}, status=400)
            return

        if path == "/favicon.ico":
            self._send(204)
            return

        if path == "/health":
            self._send_json({"ok": True, "server": "request-lab",
                             "version": VERSION, "requests_version": requests.__version__})
            return

        if path == "/headers":
            text = self._raw_head().decode("latin-1")
            self._send_text(text, content_type="text/plain; charset=iso-8859-1")
            return

        if path == "/" and self.command in ("GET", "HEAD"):
            self._send_html(self._landing_page())
            return

        if path.startswith("/status/"):
            self._handle_status(path)
            return

        if path.startswith("/redirect/"):
            self._handle_redirect(path)
            return

        if path.startswith("/delay/"):
            self._handle_delay(path)
            return

        if path.startswith("/basic-auth/"):
            self._handle_basic_auth(path)
            return

        if path == "/cookies/set":
            self._handle_cookie_set(query)
            return

        if path == "/json":
            self._send_json({
                "ok": True,
                "message": "这是服务器返回的 JSON，不是回显。",
                "items": [{"id": 1, "name": "alpha"}, {"id": 2, "name": "中文"}],
                "nested": {"flag": True, "none": None, "number": 3.14},
            })
            return

        if path == "/proxy":
            self._handle_proxy(query)
            return

        # /echo 以及任何其他路径都回显，方便直接拿任意 URL 做实验。
        request_data = self._echo_payload(path, query, body, truncated, declared)
        self._send_json({"ok": True, "request": request_data})

    # ----- 演练接口 --------------------------------------------------------

    def _handle_status(self, path: str) -> None:
        raw = path.rsplit("/", 1)[-1]
        try:
            code = int(raw)
        except ValueError:
            self._send_json({"ok": False, "error": "状态码必须是整数"}, status=400)
            return
        if code < 200 or code > 599:
            self._send_json({"ok": False, "error": "状态码范围是 200-599"}, status=400)
            return
        try:
            phrase = HTTPStatus(code).phrase
        except ValueError:
            phrase = "Unknown Status"
        payload = {"ok": 200 <= code < 400, "status": code, "phrase": phrase}
        self._send_json(payload, status=code)

    def _handle_redirect(self, path: str) -> None:
        raw = path.rsplit("/", 1)[-1]
        try:
            remaining = int(raw)
        except ValueError:
            self._send_json({"ok": False, "error": "跳转次数必须是整数"}, status=400)
            return
        remaining = max(0, min(remaining, 10))
        if remaining <= 0:
            self._send_json({"ok": True, "message": "不跳转",
                             "remaining": 0, "location": "/redirect/0"})
            return
        if remaining == 1:
            location = "/echo?from_redirect=1"
        else:
            location = f"/redirect/{remaining - 1}"
        self._send_json(
            {"ok": True, "message": "302 跳转", "location": location,
             "remaining": remaining - 1},
            status=302,
            headers={"Location": location},
        )

    def _handle_delay(self, path: str) -> None:
        raw = path.rsplit("/", 1)[-1]
        try:
            seconds = float(raw)
        except ValueError:
            self._send_json({"ok": False, "error": "延迟必须是数字（秒）"}, status=400)
            return
        seconds = max(0.0, min(seconds, 10.0))
        time.sleep(seconds)
        self._send_json({"ok": True, "delayed_seconds": seconds})

    def _handle_basic_auth(self, path: str) -> None:
        rest = path[len("/basic-auth/"):]
        username, _, password = rest.partition("/")
        auth = self._authorization()
        supplied_user = (auth or {}).get("username")
        supplied_pass = (auth or {}).get("password")

        if (auth or {}).get("scheme") != "Basic" or supplied_user is None \
                or not hmac.compare_digest(str(supplied_user), username) \
                or not hmac.compare_digest(str(supplied_pass), password):
            self._send_json(
                {"ok": False, "error": "unauthorized",
                 "message": "需要正确的 Basic Auth", "realm": "request-lab"},
                status=401,
                headers={"WWW-Authenticate": 'Basic realm="request-lab", charset="UTF-8"'},
            )
            return
        self._send_json({"ok": True, "message": "认证成功",
                         "username": username, "authorization": auth})

    def _handle_cookie_set(self, query: dict[str, list[str]]) -> None:
        if not query:
            self._send_json({"ok": False, "error": "至少提供一个 cookie 参数"}, status=400)
            return

        cookie_headers: list[tuple[str, str]] = []
        for name, values in query.items():
            if not re.fullmatch(r"[!#$%&'*+\-.^_`|~0-9A-Za-z]+", name):
                self._send_json({"ok": False, "error": f"非法 cookie 名: {name}"},
                                status=400)
                return
            for value in values:
                jar = SimpleCookie()
                jar[name] = value
                header_value = jar.output(header="").strip()
                attributes = "Path=/; HttpOnly; SameSite=Lax"
                if self._scheme() == "https":
                    attributes += "; Secure"
                cookie_headers.append(("Set-Cookie", f"{header_value}; {attributes}"))

        self.send_response(200)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        payload = {"ok": True, "cookies": query,
                   "note": "响应中已发送 Set-Cookie，下一次请求带上 Cookie 即可验证。"}
        body = json.dumps(payload, ensure_ascii=False, indent=2).encode("utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Request-Lab", VERSION)
        for name, value in cookie_headers:
            self.send_header(name, value)
        if self.close_connection:
            self.send_header("Connection", "close")
        self.end_headers()
        self._response_started = True
        if self.command != "HEAD":
            self.wfile.write(body)

    def _handle_proxy(self, query: dict[str, list[str]]) -> None:
        target = query.get("url", [None])[0]
        if not target:
            self._send_json({
                "ok": False,
                "error": "缺少 url 参数",
                "example": "/proxy?url=https://httpbin.org/get",
            }, status=400)
            return

        parsed = urlsplit(target)
        if parsed.scheme not in ("http", "https") or not parsed.netloc:
            self._send_json({"ok": False, "error": "url 必须是 http:// 或 https:// 地址"},
                            status=400)
            return

        method = query.get("method", ["GET"])[0].upper()
        if method not in {"GET", "HEAD", "POST", "PUT", "PATCH", "DELETE", "OPTIONS"}:
            self._send_json({"ok": False, "error": f"不支持的 method: {method}"}, status=400)
            return

        try:
            timeout = max(1.0, min(float(query.get("timeout", ["8"])[0]), 30.0))
        except ValueError:
            timeout = 8.0
        verify = query.get("verify", ["1"])[0].lower() not in ("0", "false", "no")
        allow_redirects = query.get("allow_redirects", ["1"])[0].lower() \
            not in ("0", "false", "no")

        started = time.perf_counter()
        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                with requests.Session() as session:
                    session.trust_env = False
                    response = session.request(
                        method,
                        target,
                        timeout=timeout,
                        verify=verify,
                        allow_redirects=allow_redirects,
                        stream=True,
                        headers={
                            "User-Agent": f"request-lab-proxy/{VERSION}",
                            "Accept": "*/*",
                        },
                    )
                    try:
                        raw = response.raw.read(PROXY_PREVIEW + 1, decode_content=True)
                    finally:
                        response.close()
            elapsed_ms = round((time.perf_counter() - started) * 1000, 2)

            preview, encoding = self._decode_text(raw[:PROXY_PREVIEW],
                                                  response.headers.get("Content-Type"))
            result: dict[str, Any] = {
                "ok": True,
                "request": {
                    "method": response.request.method,
                    "url": response.request.url,
                    "headers": [{"name": k, "value": v}
                                for k, v in response.request.headers.items()],
                },
                "response": {
                    "status": response.status_code,
                    "reason": response.reason,
                    "http_version": "HTTP/1.1" if response.raw.version == 11 else str(response.raw.version),
                    "elapsed_ms": elapsed_ms,
                    "headers": [{"name": k, "value": v}
                                for k, v in response.headers.items()],
                    "body_size_at_least": len(raw),
                    "body_truncated": len(raw) > PROXY_PREVIEW,
                    "body_text": preview,
                    "body_text_encoding": encoding,
                    "url": response.url,
                },
                "history": [
                    {"status": item.status_code, "url": item.url}
                    for item in response.history
                ],
                "proxy_options": {
                    "verify": verify,
                    "allow_redirects": allow_redirects,
                    "timeout": timeout,
                },
            }
            if preview is None:
                result["response"]["body_base64"] = base64.b64encode(
                    raw[:4096]).decode("ascii")
            self._send_json(result)
        except requests.RequestException as exc:
            self._send_json({
                "ok": False,
                "error": type(exc).__name__,
                "message": str(exc),
                "hint": "如果是自签名 HTTPS，可加 &verify=0；检查目标地址和网络。",
            }, status=502)

    # ----- 首页 ------------------------------------------------------------

    def _landing_page(self) -> str:
        host_header = self.headers.get("Host", "")
        hostname = urlsplit(f"//{host_header}").hostname if host_header else ""
        if not hostname:
            hostname = self.server.server_address[0]
        if ":" in hostname and not hostname.startswith("["):
            hostname = f"[{hostname}]"

        http_port = getattr(self.server, "lab_http_port", None)
        https_port = getattr(self.server, "lab_https_port", None)
        http_base = f"http://{hostname}:{http_port}" if http_port else "（HTTP 未启用）"
        https_base = f"https://{hostname}:{https_port}" if https_port else "（HTTPS 未启用）"

        page = LANDING_PAGE
        page = page.replace("{{HTTP_BASE}}", http_base)
        page = page.replace("{{HTTPS_BASE}}", https_base)
        page = page.replace("{{HTTP_PORT}}", str(http_port or "-"))
        page = page.replace("{{HTTPS_PORT}}", str(https_port or "-"))
        return page

    def _send_html(self, text: str) -> None:
        self._send_text(text, content_type="text/html; charset=utf-8")

    # ----- HTTP 方法 -------------------------------------------------------

    def do_GET(self) -> None:
        self._dispatch()

    def do_HEAD(self) -> None:
        self._dispatch()

    def do_POST(self) -> None:
        self._dispatch()

    def do_PUT(self) -> None:
        self._dispatch()

    def do_PATCH(self) -> None:
        self._dispatch()

    def do_DELETE(self) -> None:
        self._dispatch()

    def do_OPTIONS(self) -> None:
        self._dispatch()


LANDING_PAGE = """<!doctype html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>requests 练习服务器</title>
<style>
  :root { color-scheme: light dark; }
  body { max-width: 980px; margin: 0 auto; padding: 28px 20px 64px;
         font: 15px/1.65 -apple-system, BlinkMacSystemFont, "Segoe UI",
               "Noto Sans CJK SC", "Microsoft YaHei", sans-serif; }
  h1 { margin-bottom: 4px; }
  .sub { color: #777; margin-top: 0; }
  .url { display: inline-block; padding: 6px 10px; border-radius: 8px;
         background: rgba(127,127,127,.12); font-family: ui-monospace, monospace; }
  pre { padding: 14px 16px; overflow-x: auto; border-radius: 10px;
        background: #111827; color: #e5e7eb; font-size: 13px; line-height: 1.55; }
  code { font-family: ui-monospace, SFMono-Regular, Consolas, monospace; }
  table { width: 100%; border-collapse: collapse; margin: 12px 0 28px; }
  th, td { text-align: left; border-bottom: 1px solid rgba(127,127,127,.25);
           padding: 8px 10px; vertical-align: top; }
  th { font-weight: 600; }
  td code { white-space: nowrap; }
  .note { border-left: 4px solid #e0a800; padding: 10px 14px;
          background: rgba(224,168,0,.09); border-radius: 0 8px 8px 0; }
  .ok { color: #198754; font-weight: 600; }
</style>
</head>
<body>
  <h1>requests 练习服务器 <span class="ok">● 运行中</span></h1>
  <p class="sub">发送请求，然后查看服务器收到的真实请求行、请求头、Cookie、认证信息和请求体。</p>

  <p>HTTP 基址：<span class="url">{{HTTP_BASE}}</span><br>
     HTTPS 基址：<span class="url">{{HTTPS_BASE}}</span></p>

  <div class="note">
    HTTPS 使用脚本自动生成的自签名证书。用 requests 练习时：
    <code>verify=False</code>（仅限本机实验）。浏览器会提示证书不受信任。
  </div>

  <h2>最快开始</h2>
<pre><code>import requests

r = requests.get(
    "{{HTTP_BASE}}/echo",
    params={"q": "hello", "page": 2},
    headers={"X-Practice": "yes"},
    cookies={"sid": "abc"},
    timeout=5,
)
print(r.status_code)
print(r.json()["request"]["raw_head"])
</code></pre>

<pre><code># HTTPS + POST JSON + Basic Auth
r = requests.post(
    "{{HTTPS_BASE}}/echo?from=https",
    json={"name": "小明", "n": 42},
    auth=("alice", "secret"),
    verify=False,
)
print(r.json()["request"]["body"]["json"])
</code></pre>

  <h2>接口</h2>
  <table>
    <tr><th>接口</th><th>作用</th></tr>
    <tr><td><code>/echo</code> 或任意路径</td>
        <td>回显完整请求：<code>request.raw_head</code>、<code>headers</code>、<code>headers_by_name</code>、<code>query</code>、<code>cookie</code>、<code>authorization</code>、<code>body</code>、<code>tls</code>。</td></tr>
    <tr><td><code>/headers</code></td><td>只返回原始请求行和请求头文本，适合逐个字段检查。</td></tr>
    <tr><td><code>/status/418</code></td><td>返回指定状态码（200-599）。</td></tr>
    <tr><td><code>/redirect/2</code></td><td>连续 302 跳转，测试 <code>allow_redirects</code> 和 <code>history</code>。</td></tr>
    <tr><td><code>/delay/1.5</code></td><td>延迟最多 10 秒，测试 <code>timeout</code>。</td></tr>
    <tr><td><code>/basic-auth/alice/secret</code></td><td>测试 Basic Auth。</td></tr>
    <tr><td><code>/cookies/set?sid=abc</code></td><td>返回 Set-Cookie，测试 Session 持久化。</td></tr>
    <tr><td><code>/json</code></td><td>返回固定 JSON，测试解析。</td></tr>
    <tr><td><code>/proxy?url=…</code></td><td>服务器内部用 <b>requests</b> 请求目标地址，回显它实际发出的请求头和收到的响应。</td></tr>
    <tr><td><code>/health</code></td><td>服务状态。</td></tr>
  </table>

  <h2>抓包式检查</h2>
<pre><code>r = requests.post("{{HTTP_BASE}}/echo?tag=demo",
                  headers={"X-Token": "abc", "X-Dup": "one"},
                  data={"a": "1", "b": "二"})
req = r.json()["request"]
print(req["raw_head"])          # 原始请求行 + 请求头
print(req["headers_by_name"])   # 重复头、大小写一次看全
print(req["body"]["form"])      # 表单解析结果
</code></pre>

  <p class="sub">所有数据只保存在内存中，不落盘。默认只监听 127.0.0.1。</p>
</body>
</html>
"""


# ---------------------------------------------------------------------------
# 服务器启动与证书
# ---------------------------------------------------------------------------


class LabHTTPServer(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = True


def ensure_certificate(cert_dir: Path) -> tuple[Path, Path]:
    cert_dir.mkdir(parents=True, exist_ok=True)
    cert_file = cert_dir / "cert.pem"
    key_file = cert_dir / "key.pem"

    if cert_file.is_file() and key_file.is_file():
        return cert_file, key_file

    command = [
        "openssl", "req", "-x509", "-newkey", "rsa:2048", "-sha256",
        "-days", "365", "-nodes",
        "-keyout", str(key_file),
        "-out", str(cert_file),
        "-subj", "/CN=localhost",
        "-addext", "subjectAltName=DNS:localhost,IP:127.0.0.1",
    ]
    try:
        completed = subprocess.run(command, capture_output=True, text=True,
                                   check=False, timeout=30)
    except FileNotFoundError as exc:
        raise RuntimeError("系统找不到 openssl，无法生成 HTTPS 证书") from exc
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError("openssl 生成证书超时") from exc

    if completed.returncode != 0:
        raise RuntimeError(f"openssl 生成证书失败：{completed.stderr.strip()}")

    os.chmod(key_file, 0o600)
    return cert_file, key_file


def _make_tls_context(cert_file: Path, key_file: Path) -> ssl.SSLContext:
    context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
    context.minimum_version = ssl.TLSVersion.TLSv1_2
    context.load_cert_chain(certfile=str(cert_file), keyfile=str(key_file))
    context.set_alpn_protocols(["http/1.1"])
    return context


def _display_host(host: str) -> str:
    if host in ("0.0.0.0", "::"):
        return "127.0.0.1"
    return f"[{host}]" if ":" in host and not host.startswith("[") else host


def start_servers(args: argparse.Namespace) -> tuple[list[LabHTTPServer], list[threading.Thread]]:
    servers: list[LabHTTPServer] = []
    threads: list[threading.Thread] = []
    http_port: int | None = None
    https_port: int | None = None

    if not args.no_http:
        http_server = LabHTTPServer((args.host, args.http_port), LabHandler)
        servers.append(http_server)
        http_port = http_server.server_port

    if not args.no_https:
        try:
            cert_file, key_file = ensure_certificate(args.cert_dir)
            tls_context = _make_tls_context(cert_file, key_file)
            https_server = LabHTTPServer((args.host, args.https_port), LabHandler)
            https_server.socket = tls_context.wrap_socket(
                https_server.socket, server_side=True)
            servers.append(https_server)
            https_port = https_server.server_port
        except (OSError, RuntimeError, ssl.SSLError) as exc:
            print(f"[!] HTTPS 未能启动：{exc}", file=sys.stderr)
            if args.no_http:
                raise

    for server in servers:
        server.lab_http_port = http_port
        server.lab_https_port = https_port
        server.lab_scheme = "https" if https_port == server.server_port else "http"

    for server in servers:
        thread = threading.Thread(target=server.serve_forever,
                                  name=f"request-lab-{server.server_port}",
                                  daemon=True)
        thread.start()
        threads.append(thread)

    return servers, threads


def print_startup(args: argparse.Namespace, servers: list[LabHTTPServer]) -> None:
    display = _display_host(args.host)
    print("=" * 68)
    print(f" requests 练习服务器 v{VERSION}")
    print("=" * 68)
    for server in servers:
        scheme = getattr(server, "lab_scheme", "http")
        print(f"  {scheme.upper():5s}  {scheme}://{display}:{server.server_port}/")
    print()
    print("  回显请求头：      /echo  （任意路径也会回显）")
    print("  纯文本头：        /headers")
    print("  用 requests 代发： /proxy?url=https://httpbin.org/get")
    print("  首页与示例：      /")
    print()
    print("  提示：把 requests 的 headers、params、json、data、files、auth、")
    print("        cookies 发到 /echo，然后对照 request.raw_head 检查。")
    if args.host not in ("127.0.0.1", "localhost", "::1"):
        print()
        print("  [!] 当前绑定到非本机地址；/proxy 可能被他人用作网络代理。")
    print("=" * 68)
    print("  按 Ctrl+C 停止")
    print(flush=True)


def stop_servers(servers: list[LabHTTPServer], threads: list[threading.Thread]) -> None:
    for server in servers:
        try:
            server.shutdown()
        except Exception:
            pass
    for server in servers:
        try:
            server.server_close()
        except Exception:
            pass
    for thread in threads:
        thread.join(timeout=3)


# ---------------------------------------------------------------------------
# 自检
# ---------------------------------------------------------------------------


def _demo_summary(label: str, response: requests.Response) -> None:
    payload = response.json()
    req = payload["request"]
    print(f"  [ok] {label:<18} -> {response.status_code} "
          f"{req['method']} {req['raw_path']}")
    checks = req["headers_by_name"]
    for header in ("x-practice", "content-type", "authorization", "cookie"):
        if header in checks:
            value = checks[header][0]
            if header == "authorization" and len(value) > 48:
                value = value[:45] + "..."
            print(f"         {header}: {value}")
    if req["body"].get("json") is not None:
        print(f"         body.json: {req['body']['json']}")
    if req["body"].get("form"):
        print(f"         body.form: {req['body']['form']}")
    if req["body"].get("multipart", {}).get("files"):
        files = req["body"]["multipart"]["files"]
        print(f"         files: {[f['filename'] for f in files]}")


def run_demo(args: argparse.Namespace, servers: list[LabHTTPServer]) -> None:
    http_server = next((s for s in servers
                        if getattr(s, "lab_http_port", None) == s.server_port), None)
    https_server = next((s for s in servers
                         if getattr(s, "lab_https_port", None) == s.server_port), None)
    display = _display_host(args.host)
    http_base = f"http://{display}:{http_server.server_port}" if http_server else None
    https_base = f"https://{display}:{https_server.server_port}" if https_server else None

    print("\n--- requests 自检开始 ---", flush=True)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        with requests.Session() as session:
            session.trust_env = False

            assert http_base
            response = session.get(
                f"{http_base}/echo",
                params={"hello": "world", "page": "2"},
                headers={"X-Practice": "yes"},
                cookies={"sid": "abc"},
                timeout=5,
            )
            response.raise_for_status()
            req = response.json()["request"]
            assert req["headers_by_name"]["x-practice"] == ["yes"]
            assert req["query"]["hello"] == ["world"]
            assert req["cookie"]["sid"] == "abc"
            _demo_summary("GET 头/参数/Cookie", response)

            response = session.post(
                f"{http_base}/echo?from=demo",
                json={"name": "小明", "n": 42},
                headers={"X-Practice": "json"},
                timeout=5,
            )
            response.raise_for_status()
            assert response.json()["request"]["body"]["json"] == {"name": "小明", "n": 42}
            _demo_summary("POST JSON", response)

            response = session.post(
                f"{http_base}/echo",
                data={"a": "1", "b": "二"},
                timeout=5,
            )
            response.raise_for_status()
            assert response.json()["request"]["body"]["form"]["b"] == ["二"]
            _demo_summary("POST 表单", response)

            response = session.post(
                f"{http_base}/echo",
                files={"file": ("hello.txt", b"hello requests", "text/plain")},
                data={"note": "upload"},
                timeout=5,
            )
            response.raise_for_status()
            files = response.json()["request"]["body"]["multipart"]["files"]
            assert files[0]["filename"] == "hello.txt"
            _demo_summary("POST 文件", response)

            response = session.get(
                f"{http_base}/basic-auth/alice/secret",
                auth=("alice", "secret"),
                timeout=5,
            )
            response.raise_for_status()
            print(f"  [ok] Basic Auth         -> {response.status_code} "
                  f"{response.json()['message']}")

            response = session.get(f"{http_base}/redirect/2", timeout=5)
            response.raise_for_status()
            assert len(response.history) == 2
            print(f"  [ok] 重定向              -> 200（history={len(response.history)}）")

            response = session.get(f"{http_base}/status/418", timeout=5)
            assert response.status_code == 418
            print("  [ok] 状态码              -> 418 I'm a Teapot")

            response = session.get(f"{http_base}/cookies/set", params={"sid": "xyz"},
                                   timeout=5)
            response.raise_for_status()
            response = session.get(f"{http_base}/echo", timeout=5)
            response.raise_for_status()
            assert response.json()["request"]["cookie"]["sid"] == "xyz"
            print("  [ok] Set-Cookie 持久化   -> sid=xyz")

            response = session.get(f"{http_base}/proxy",
                                   params={"url": f"{http_base}/json"}, timeout=10)
            response.raise_for_status()
            proxy = response.json()
            assert proxy["response"]["status"] == 200
            print(f"  [ok] requests 代理       -> 内部 requests 状态 "
                  f"{proxy['response']['status']}，"
                  f"{proxy['response']['elapsed_ms']} ms")

            response = session.get(f"{http_base}/echo", timeout=5)
            jar = session.cookies.get_dict()
            if jar:
                print(f"  [ok] 会话 Cookie         -> {jar}")

            if https_base:
                response = session.get(f"{https_base}/echo?via=tls", verify=False,
                                       timeout=5)
                response.raise_for_status()
                tls = response.json()["request"]["tls"]
                assert tls["enabled"] is True
                print(f"  [ok] HTTPS               -> {tls['version']} / {tls['cipher']}")

    print("--- 自检通过，服务器即将停止 ---\n", flush=True)


# ---------------------------------------------------------------------------
# 命令行
# ---------------------------------------------------------------------------


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="本地 HTTP/HTTPS 请求头回显服务器，用于练习 Python requests。",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--host", default="127.0.0.1",
                        help="监听地址；仅在明确需要时改成 0.0.0.0")
    parser.add_argument("--http-port", type=int, default=8000, help="HTTP 端口")
    parser.add_argument("--https-port", type=int, default=8443, help="HTTPS 端口")
    parser.add_argument("--no-http", action="store_true", help="不启动 HTTP")
    parser.add_argument("--no-https", action="store_true", help="不启动 HTTPS")
    parser.add_argument("--cert-dir", type=Path,
                        default=SCRIPT_DIR / ".request_lab_certs",
                        help="自签名证书目录")
    parser.add_argument("--demo", action="store_true",
                        help="启动后用 requests 自动跑一遍自检，然后退出")
    args = parser.parse_args(argv)
    if args.no_http and args.no_https:
        parser.error("--no-http 和 --no-https 不能同时使用")
    return args


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    servers: list[LabHTTPServer] = []
    threads: list[threading.Thread] = []

    try:
        servers, threads = start_servers(args)
        print_startup(args, servers)

        if args.demo:
            run_demo(args, servers)
        else:
            while True:
                time.sleep(3600)
    except KeyboardInterrupt:
        print("\n已停止。")
    except OSError as exc:
        print(f"[!] 启动失败：{exc}", file=sys.stderr)
        return 1
    finally:
        stop_servers(servers, threads)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
