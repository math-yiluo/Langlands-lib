/-
Ported from `Theorems/Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean` (entire file, 9
lines) of the Anthropic Lean formalization of Fermat's Last Theorem: registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
original file SHA256 74e59e6b55f087f94438d17b1d47b7845b6783866d835d02c5eae980d79e0a67.
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
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`. The
  audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the proof `by p2m_exact_reverting
  @_root_.P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.solution` was replaced by `apply
  @_root_.P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.solution <;> assumption`.

Declaration names and namespaces are unchanged. Apart from the universe generalization, the
mathematical hypotheses and conclusions of the source are retained.
-/
import Langlands.AnthropicFLT.Definitions.Def_FrobeniusDensity_PrimeSums
import Langlands.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open Filter Topology Asymptotics
theorem FrobeniusDensity.primeSum_toReal_add_log_isBigO
    (K : Type u) [Field K] [NumberField K] :
    (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1:ℝ)) := by
  apply @_root_.P2MW.S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.solution <;> assumption
