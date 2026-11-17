# A continuous logarithm of a ray class L-series: proof

This module proves `solution`, the statement of `NumberField.exists_continuousOn_exp_eq_rayClassLSeries` (see that wrapper module). Its auxiliary declarations live in the namespace `P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries`.

The proof sets Λ(s) = Σ_v −log(1 − χ(v)·N(v)^(−s)) over height-one primes v. It proves absolute summability of the ideal series for s > 1 and unique factorization of integral ideals. Finite Euler products, exhausted by norm, then give exp Λ(s) = L(s, χ). Λ is continuous on (1, ∞). For s ≥ 1 each prime term has norm at most 1/2, so the difference between Λ(s) and the prime sum Σ_v χ(v)·N(v)^(−s) is bounded by a constant multiple of Σ_v N(v)^(−2). This proves the stated bound uniformly in s > 1.

Source: `P2M/Sol/S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean` (entire file, 684 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `3f901fdb86e3f8c66969945235499b945ca39fade8dcf5336634703b65ccbb85`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped and its commands are replaced by ordinary Lean commands: 2 `p2m_export` commands by `export _root_.… (…)`. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
