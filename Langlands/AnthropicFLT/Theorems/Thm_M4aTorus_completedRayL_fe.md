# Analytic continuation and functional equation of completed ray class L-functions

`M4aTorus.completedRayL_fe`: let K be a number field, 𝔣 an ideal, χ a character of the narrow ray class group modulo 𝔣, and S a set of real places with `M4aP2.IsParity K 𝔣 χ S`. Then there are F, G : ℂ → ℂ with the following properties.
- F and G are complex differentiable on ℂ ∖ {0, 1}.
- For Re s > 1, F(s) is the completed L-function of χ and G(s) that of the conjugate character χ̄.
- If 𝔣 ≠ 0, 𝔣 ≠ (1), χ is primitive (`M4aP2.IsPrimitiveMod`) and y₀ is a Gauss datum, then for s ≠ 0, 1: F(1 − s) = (−i)^|S| · (gaussSumAt(y₀)/√N(𝔣)) · G(s).
- If χ ≠ 1, F and G are entire.

The proof applies the solution module.

Source: `Theorems/Thm_M4aTorus_completedRayL_fe.lean` (entire file, 23 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `3347c29df9a85cc5a5b098c1fdb85a2a005cf1bac9ad5aa259e5d886fc411e6e`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the proof `by p2m_exact_reverting @_root_.P2MW.S_M4aTorus_completedRayL_fe.solution` was replaced by `apply @_root_.P2MW.S_M4aTorus_completedRayL_fe.solution <;> assumption`.
