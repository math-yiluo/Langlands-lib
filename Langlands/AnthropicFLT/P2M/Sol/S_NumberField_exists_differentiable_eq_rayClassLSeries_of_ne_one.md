# Entire continuation of nontrivial ray class L-series: proof

This module proves `solution`, the statement of `NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one`. It uses only the last clause of `M4aTorus.completedRayL_fe`: for χ ≠ 1 the continuation F of the completed L-function is entire. It multiplies F by the entire function `recipFactor`, x^(−s/2)·Γ_ℝ(s)^(−a)·Γ_ℝ(s+1)^(−b)·(Γ_ℝ(s)Γ_ℝ(s+1))^(−c), with x = |d_K|·N(𝔣), a = r₁ − |S|, b = |S| and c = r₂. Since Γ_ℂ(s) = Γ_ℝ(s)·Γ_ℝ(s + 1), this product is the inverse of the gamma and discriminant factor for Re s > 0. The functional equation and the Gauss data are not used.

Source: `P2M/Sol/S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.lean` (entire file, 102 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `e2d5212a5c768cc40b8eb679bbccb921d3fe5c4c2e1fab0a25a7c3e950fe7892`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
