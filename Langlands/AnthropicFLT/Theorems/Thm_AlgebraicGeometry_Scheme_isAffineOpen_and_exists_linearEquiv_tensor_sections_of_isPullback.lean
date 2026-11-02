/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback
    {R : Type u} [CommRing R] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of R)) (fY : Y ⟶ Spec (CommRingCat.of R))
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (U : X.Opens) (hU : IsAffineOpen U) (V : Y.Opens) (hV : IsAffineOpen V) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom fX U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom fY V
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (p₁ ≫ fX) (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    IsAffineOpen (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) ∧
    ∃ Φ : Γ(X, U) ⊗[R] Γ(Y, V) ≃ₗ[R] Γ(P, p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V),
      ∀ (a : Γ(X, U)) (b : Γ(Y, V)), Φ (a ⊗ₜ[R] b) =
        (p₁.appLE U (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_left).hom a *
          (p₂.appLE V (p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V) inf_le_right).hom b :=
  P2MW.S_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback.solution fX fY p₁ p₂ hP U hU V hV
