/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_isFG_hom_injective_saturated_twistGradedModule
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsFinite φ]
    (π : X ⟶ Spec (.of A)) (hπ : φ ≫ ProjSpace.π A N = π) :
    ∃ (M' : ProjSpaceCech.GradedModule A N) (ψ : ProjSpaceCech.GradedModule.Hom M' (ProjSpace.twistGradedModule φ π)),
      M'.IsFG ∧ Function.Injective ψ.toLinearMap ∧
      ∀ (j : Fin (N + 1)) (e : ℤ), ∀ x ∈ (ProjSpace.twistGradedModule φ π).grade e,
        ∃ k : ℕ, ∃ x' ∈ M'.grade (e + k), ψ.toLinearMap x' = ((ProjSpace.twistGradedModule φ π).xMul j ^ k) x :=
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule.solution φ π hπ
