/-
Ported from `Theorems/Thm_FrobeniusDensity_idealSum_ne_top.lean` (entire file, 7 lines) of the
Anthropic Lean formalization of Fermat's Last Theorem: registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
original file SHA256 09d6661a5e24a22b673bbd735d5b672f4aba0f5b4e5d77a5946bf57e244324db.
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
  @_root_.P2MW.S_FrobeniusDensity_idealSum_ne_top.solution` was replaced by `apply
  @_root_.P2MW.S_FrobeniusDensity_idealSum_ne_top.solution <;> assumption`.

Declaration names and namespaces are unchanged. Apart from the universe generalization, the
mathematical hypotheses and conclusions of the source are retained.
-/
import Langlands.AnthropicFLT.Definitions.Def_FrobeniusDensity_PrimeSums
import Langlands.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_idealSum_ne_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem FrobeniusDensity.idealSum_ne_top
    (K : Type u) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    FrobeniusDensity.idealSum K s ≠ ⊤ := by
  apply @_root_.P2MW.S_FrobeniusDensity_idealSum_ne_top.solution <;> assumption
