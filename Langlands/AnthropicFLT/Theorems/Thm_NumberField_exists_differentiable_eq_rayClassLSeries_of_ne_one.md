# Entire continuation of nontrivial ray class L-series

`NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one`: let K be a number field, 𝔣 ≠ 0 an ideal, χ ≠ 1 a character of the narrow ray class group modulo 𝔣, and S a set of real places with the parity property. Then there is an entire function g with g(s) = L(s, χ) for Re s > 1. The proof applies the solution module.

Source: `Theorems/Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.lean` (entire file, 16 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `54d0dda02818c9331a3ce68a0c92de07816b75bb7a299e0a6c28700a1934a4c4`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the proof `by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.solution` was replaced by `apply @_root_.P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.solution <;> assumption`.
