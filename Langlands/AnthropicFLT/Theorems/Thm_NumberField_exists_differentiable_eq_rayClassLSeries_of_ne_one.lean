/-
Ported from `Theorems/Thm_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.lean`
(entire file, 16 lines) of the Anthropic Lean formalization of Fermat's Last Theorem: registered
source `anthropic-flt-complete-lean-source-6e837e75`, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, original file SHA256
54d0dda02818c9331a3ce68a0c92de07816b75bb7a299e0a6c28700a1934a4c4.
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
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`. The
  audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the proof `by p2m_exact_reverting
  @_root_.P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.solution` was
  replaced by `apply
  @_root_.P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.solution <;>
  assumption`.

Declaration names and namespaces are unchanged. Apart from the universe generalization, the
mathematical hypotheses and conclusions of the source are retained.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_NumberField_CompletedRayL
import Langlands.AnthropicFLT.Definitions.Def_NumberField_RayCharacterData
import Langlands.AnthropicFLT.P2M.Sol.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

set_option autoImplicit false

open NumberField NumberField.InfinitePlace Deep.NTSupply

theorem NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one
    (K : Type u) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) (hχ : χ ≠ 1)
    (S : Finset {w : InfinitePlace K // w.IsReal}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ s : ℂ, 1 < s.re → g s = M4aTorus.rayClassLSeries K 𝔣 χ s := by
  apply @_root_.P2MW.S_NumberField_exists_differentiable_eq_rayClassLSeries_of_ne_one.solution <;> assumption
