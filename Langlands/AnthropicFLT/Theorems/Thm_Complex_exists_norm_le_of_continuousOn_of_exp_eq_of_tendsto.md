# Local boundedness of a continuous logarithm with nonzero limit

`Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto`: let Λ, ℓ : ℝ → ℂ and a ∈ ℝ, with Λ continuous on (a, ∞) and exp Λ(s) = ℓ(s) for s > a. If ℓ(s) tends to c ≠ 0 as s → a⁺, then there are C and δ > 0 with ‖Λ(s)‖ ≤ C for a < s < a + δ. The proof applies the solution module.

Source: `Theorems/Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.lean` (entire file, 11 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `b46c82d045a1bbb183217a8a16715b5e62696c371c2b4e1c97a9257b236f7bb7`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. The mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Cleanup: the proof `by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.solution` was replaced by `apply @_root_.P2MW.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.solution <;> assumption`.
