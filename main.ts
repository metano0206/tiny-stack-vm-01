// Tiny stack VM: an interpreter for make.fun's tiny stack ISA, version 1.
// One run answers every instance in /input: for each <id> it runs
// /input/<id>/program.bin on /input/<id>/input.bin and writes
// /output/<id>/stdout.bin (the bytes the program wrote) and
// /output/<id>/exit.txt (its exit code in decimal).
import { readFileSync, writeFileSync, mkdirSync, readdirSync } from "node:fs";

const OUT_MAX = 65536; // output limit in bytes
const STEP_MAX = 1000000; // executed-instruction limit

// Run one program; returns [outputBytes, exitCode]. A trap ends the run
// with the trap's code and keeps the output written before it.
function run(P, I) {
  const S = new Int32Array(256); // data stack, sp values deep
  const C = []; // call stack of return addresses
  const M = new Int32Array(256); // memory words, all zero
  const O = new Uint8Array(OUT_MAX); // output bytes, ol of them
  let sp = 0, ol = 0, pc = 0, ii = 0, steps = 0;
  const n = P.length;
  for (;;) {
    if (steps >= STEP_MAX) return [O.subarray(0, ol), 10];
    if (pc < 0 || pc >= n) return [O.subarray(0, ol), 9];
    const op = P[pc];
    // Immediate length, and the unknown-opcode trap (5) before the
    // immediate-fit trap (9), as the ISA's step order prescribes.
    let il;
    if (op === 0x01) il = 1;
    else if (op === 0x02) il = 4;
    else if (op >= 0x30 && op <= 0x33) il = 2;
    else if (op <= 0x07 || (op >= 0x10 && op <= 0x22) || op === 0x34 ||
             op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53)) il = 0;
    else return [O.subarray(0, ol), 5];
    if (pc + 1 + il > n) return [O.subarray(0, ol), 9];
    steps++;
    const nx = pc + 1 + il; // address of the next instruction
    if (op === 0x00) return [O.subarray(0, ol), 0]; // HALT
    if (op === 0x01 || op === 0x02) { // PUSH8 / PUSH32
      if (sp >= 256) return [O.subarray(0, ol), 3];
      S[sp++] = op === 0x01
        ? (P[pc + 1] << 24) >> 24
        : P[pc + 1] | P[pc + 2] << 8 | P[pc + 3] << 16 | P[pc + 4] << 24;
      pc = nx; continue;
    }
    if (op >= 0x03 && op <= 0x07) { // POP DUP SWAP OVER ROT
      const need = op === 0x03 || op === 0x04 ? 1 : op === 0x07 ? 3 : 2;
      if (sp < need) return [O.subarray(0, ol), 2];
      if ((op === 0x04 || op === 0x06) && sp >= 256) return [O.subarray(0, ol), 3];
      if (op === 0x03) sp--;
      else if (op === 0x04) { S[sp] = S[sp - 1]; sp++; }
      else if (op === 0x05) { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; }
      else if (op === 0x06) { S[sp] = S[sp - 2]; sp++; }
      else { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; }
      pc = nx; continue;
    }
    if (op === 0x17 || op === 0x1b) { // NEG / NOT
      if (sp < 1) return [O.subarray(0, ol), 2];
      S[sp - 1] = op === 0x17 ? (-S[sp - 1]) | 0 : ~S[sp - 1];
      pc = nx; continue;
    }
    if ((op >= 0x10 && op <= 0x22)) { // binary arithmetic and comparison
      if (sp < 2) return [O.subarray(0, ol), 2];
      const b = S[--sp], a = S[sp - 1];
      let r;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) { if (b === 0) return [O.subarray(0, ol), 4]; r = Math.trunc(a / b) | 0; }
      else if (op === 0x14) { if (b === 0) return [O.subarray(0, ol), 4]; r = (a % b) | 0; }
      else if (op === 0x15) { if (b === 0) return [O.subarray(0, ol), 4]; r = Math.trunc((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 0x16) { if (b === 0) return [O.subarray(0, ol), 4]; r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
      S[sp - 1] = r;
      pc = nx; continue;
    }
    if (op >= 0x30 && op <= 0x34) { // JMP JZ JNZ CALL RET
      const off = (P[pc + 1] | P[pc + 2] << 8) << 16 >> 16; // signed 16-bit
      if (op === 0x30) { pc = nx + off; continue; }
      if (op === 0x31 || op === 0x32) {
        if (sp < 1) return [O.subarray(0, ol), 2];
        const v = S[--sp];
        const jump = op === 0x31 ? v === 0 : v !== 0; // JZ / JNZ
        pc = jump ? nx + off : nx;
        continue;
      }
      if (op === 0x33) { // CALL: immediate is an unsigned absolute target
        if (C.length >= 64) return [O.subarray(0, ol), 7];
        C.push(nx);
        pc = P[pc + 1] | P[pc + 2] << 8;
        continue;
      }
      if (C.length === 0) return [O.subarray(0, ol), 8]; // RET
      pc = C.pop(); continue;
    }
    if (op === 0x40 || op === 0x41) { // LOAD / STORE
      if (sp < (op === 0x40 ? 1 : 2)) return [O.subarray(0, ol), 2];
      const addr = S[--sp];
      if (addr < 0 || addr > 255) return [O.subarray(0, ol), 6];
      if (op === 0x40) S[sp++] = M[addr];
      else M[addr] = S[--sp];
      pc = nx; continue;
    }
    // 0x50 PRINT, 0x51 PUTC, 0x52 IN, 0x53 EXIT
    if (op === 0x52) { // IN
      if (sp >= 256) return [O.subarray(0, ol), 3];
      S[sp++] = ii < I.length ? I[ii++] : -1;
      pc = nx; continue;
    }
    if (sp < 1) return [O.subarray(0, ol), 2];
    const v = S[--sp];
    if (op === 0x53) return [O.subarray(0, ol), v & 255]; // EXIT
    if (op === 0x51) { // PUTC
      if (ol + 1 > OUT_MAX) return [O.subarray(0, ol), 11];
      O[ol++] = v & 255;
    } else { // PRINT: v in decimal ASCII
      const s = String(v);
      if (ol + s.length > OUT_MAX) return [O.subarray(0, ol), 11];
      for (let k = 0; k < s.length; k++) O[ol++] = s.charCodeAt(k);
    }
    pc = nx;
  }
}

const ids = readdirSync("/input", { withFileTypes: true })
  .filter((d) => d.isDirectory()).map((d) => d.name).sort();
for (const id of ids) {
  // A set always ships both files; the guards keep one unreadable
  // instance from taking the other 39 answers down with it.
  let P, I;
  try { P = readFileSync(`/input/${id}/program.bin`); } catch { continue; }
  try { I = readFileSync(`/input/${id}/input.bin`); } catch { I = Buffer.alloc(0); }
  const [out, code] = run(P, I);
  mkdirSync(`/output/${id}`, { recursive: true });
  writeFileSync(`/output/${id}/stdout.bin`, out);
  writeFileSync(`/output/${id}/exit.txt`, String(code));
}
