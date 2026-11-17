# Real-valued prime sums of a number field and their elementary bounds

For a number field F, a real s and a height-one prime v, `pw F s v = N(v)^(−s)`. The module proves the following.
- N(v) ≥ 2 and 0 < pw ≤ 1 for s ≥ 0; pw is antitone in s.
- The average (1/n)·Σ_{k ≤ n} #{ideals of norm k} tends to 2^(r₁)·(2π)^(r₂)·R_K·h_K / (w_K·√|d_K|), by Mathlib's ideal counting.
- For s > 1: the families pw and n ↦ #{ideals of norm n}·n^(−s) are summable.
- The real values of `FrobeniusDensity.primeSum` and `FrobeniusDensity.tailSum` are the corresponding real series.
- `tailConst` is finite and gives the tail constant `Ctail`; the tail series is summable.

For a modulus m it proves that only finitely many primes contain m. It defines `T F m a s`, the sum of N(v)^(−s) over primes whose absolute norm is congruent to a modulo m, and `P0 F m s`, the same sum over primes not containing m. It proves that both are summable and nonnegative, and that P0 ≤ Σ pw ≤ P0 + (number of primes containing m).

Source: `Definitions/Def_NumberField_PrimeNormSums.lean` (entire file, 295 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `fad989067bef41b210c474576c12c832ebd97621807ff2065db8d4c6e45818fb`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `F` (originally `Type`) is `Type*`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
