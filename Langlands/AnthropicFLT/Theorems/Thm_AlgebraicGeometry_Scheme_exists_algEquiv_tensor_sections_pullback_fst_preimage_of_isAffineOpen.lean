/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under
the Apache License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified for this project: FLT imports are renamed to `Langlands.AnthropicFLT.*` and the FLT lakefile
options are set after the imports; any further change is listed in the paired Markdown file.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (U : X.Opens) (hU : IsAffineOpen U) (A : Type u) [CommRing A] [Algebra R A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
      ((Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U)
    ∃ e : (A ⊗[R] Γ(X, U)) ≃ₐ[A]
        Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U),
      ∀ s : Γ(X, U), e ((1 : A) ⊗ₜ[R] s) =
        ((Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app U).hom s := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen.solution R _ X c U hU A _ _
