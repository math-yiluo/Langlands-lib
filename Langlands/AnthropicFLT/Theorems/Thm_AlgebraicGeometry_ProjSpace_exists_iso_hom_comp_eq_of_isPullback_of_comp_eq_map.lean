/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
universe uz

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map
    (n : ℕ) (A B : Type uz) [CommRing A] [CommRing B] [Algebra A B] (Z : Scheme.{uz})
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (Z₁ : Scheme.{uz}) (ι₁ : Z₁ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (e₁ : Z₁ ⟶ Z)
    (h₁ : IsPullback e₁ (ι₁ ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (h₁' : e₁ ≫ ι = ι₁ ≫ ProjSpace.map A B n)
    (Z₂ : Scheme.{uz}) (ι₂ : Z₂ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (e₂ : Z₂ ⟶ Z)
    (h₂ : IsPullback e₂ (ι₂ ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (h₂' : e₂ ≫ ι = ι₂ ≫ ProjSpace.map A B n) :
    ∃ φ : Z₁ ≅ Z₂, φ.hom ≫ ι₂ = ι₁ ∧ φ.hom ≫ e₂ = e₁ :=
  P2MW.S_AlgebraicGeometry_ProjSpace_exists_iso_hom_comp_eq_of_isPullback_of_comp_eq_map.solution n A B Z ι Z₁ ι₁ e₁ h₁ h₁' Z₂ ι₂ e₂ h₂ h₂'
