/-
Ported from `Theorems/Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.lean` (entire
file, 11 lines) of the Anthropic Lean formalization of Fermat's Last Theorem: registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
original file SHA256 b46c82d045a1bbb183217a8a16715b5e62696c371c2b4e1c97a9257b236f7bb7.
Copyright 2026 Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.

Complete list of edits to the source text (the paired Markdown file gives the same list; the audit
`notes/reuse/anthropic-chebotarev-audit.md` and its evidence files `compatibility.md`,
`universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact
diffs):
- Imports of FLT modules use the `Langlands.AnthropicFLT` prefix.
- The source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set
  after the imports.
- The audit's modification comments are replaced by the port header.
- The import of `P2M.Util` is dropped.
- Cleanup: the proof `by p2m_exact_reverting
  @_root_.P2MW.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.solution` was replaced
  by `apply @_root_.P2MW.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.solution <;>
  assumption`.

Declaration names and namespaces are unchanged. The mathematical hypotheses and conclusions of the
source are retained.
-/
import Langlands.MathlibBase
import Langlands.AnthropicFLT.P2M.Sol.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
    {Λ ℓ : ℝ → ℂ} {a : ℝ} {c : ℂ} (hΛ : ContinuousOn Λ (Set.Ioi a))
    (hexp : ∀ s : ℝ, a < s → Complex.exp (Λ s) = ℓ s)
    (hlim : Filter.Tendsto ℓ (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≠ 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a < s → s < a + δ → ‖Λ s‖ ≤ C := by
  apply @_root_.P2MW.S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.solution <;> assumption
