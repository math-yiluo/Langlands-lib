/-
Ported from `Theorems/Thm_M4aTorus_completedRayL_fe.lean` (entire file, 23 lines) of the Anthropic
Lean formalization of Fermat's Last Theorem: registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
original file SHA256 3347c29df9a85cc5a5b098c1fdb85a2a005cf1bac9ad5aa259e5d886fc411e6e.
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
- Cleanup: the proof `by p2m_exact_reverting @_root_.P2MW.S_M4aTorus_completedRayL_fe.solution` was
  replaced by `apply @_root_.P2MW.S_M4aTorus_completedRayL_fe.solution <;> assumption`.

Declaration names and namespaces are unchanged. Apart from the universe generalization, the
mathematical hypotheses and conclusions of the source are retained.
-/
import Langlands.AnthropicFLT.Definitions.Def_NumberField_CompletedRayL
import Langlands.AnthropicFLT.Definitions.Def_NumberField_RayCharacterData
import Langlands.AnthropicFLT.P2M.Sol.S_M4aTorus_completedRayL_fe

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w
set_option autoImplicit false
noncomputable section
open NumberField NumberField.InfinitePlace Complex Deep.NTSupply nonZeroDivisors
theorem M4aTorus.completedRayL_fe
    (K : Type u) [Field K] [NumberField K]
    (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (S : Finset {w : InfinitePlace K // IsReal w}) (hpar : M4aP2.IsParity K 𝔣 χ S) :
    ∃ F G : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
      DifferentiableOn ℂ G {s : ℂ | s ≠ 0 ∧ s ≠ 1} ∧
      (∀ s : ℂ, 1 < s.re → F s = completedRayL K 𝔣 χ S s) ∧
      (∀ s : ℂ, 1 < s.re →
        G s = completedRayL K 𝔣 ((starRingEnd ℂ).toMonoidHom.comp χ) S s) ∧
      (∀ h𝔣 : 𝔣 ≠ ⊥, ∀ h𝔣' : 𝔣 ≠ ⊤, ∀ y₀ : K, M4aP2.IsGaussDatum K 𝔣 χ y₀ →
        M4aP2.IsPrimitiveMod K 𝔣 χ →
        ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
          F (1 - s) = (-Complex.I) ^ S.card *
            (M4aP2.gaussSumAt K 𝔣 χ h𝔣 S y₀ / (Real.sqrt (Ideal.absNorm 𝔣) : ℂ)) * G s) ∧
      (χ ≠ 1 → Differentiable ℂ F ∧ Differentiable ℂ G) := by
  apply @_root_.P2MW.S_M4aTorus_completedRayL_fe.solution <;> assumption
