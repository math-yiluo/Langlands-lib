# A continuous logarithm of a ray class L-series

`NumberField.exists_continuousOn_exp_eq_rayClassLSeries`: let K be a number field, 𝔣 ≠ 0 an ideal and χ a character of the narrow ray class group modulo 𝔣. Then there is Λ : ℝ → ℂ, continuous on (1, ∞), with the following properties.
- exp Λ(s) = L(s, χ) (`M4aTorus.rayClassLSeries`) for s > 1.
- For s > 1 the prime series Σ_v χ(v)·N(v)^(−s) is summable, with χ extended to ideals by `M4aP2.chiIdeal`.
- For some constant C, ‖Λ(s) − Σ_v χ(v)·N(v)^(−s)‖ ≤ C for all s > 1.

The proof applies the solution module.

Source: `Theorems/Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.lean` (entire file, 25 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `fd0fd915e8695c3a0cc22e4b770a7772594400fea066cf3c8959aa6f5234fd0c`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the line `attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal` was removed; the line `attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec` was removed; the proof `by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.solution` was replaced by `apply @_root_.P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.solution <;> assumption`.
