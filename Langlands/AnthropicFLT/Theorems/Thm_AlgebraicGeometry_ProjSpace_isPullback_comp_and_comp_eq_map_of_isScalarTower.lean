/-
Ported from `Theorems/Thm_AlgebraicGeometry_ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.isPullback_comp_and_comp_eq_map_of_isScalarTower
    {A : Type u} [CommRing A] (B C : Type u) [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] {n : ℕ}
    {Z ZB ZC : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) (ιB : ZB ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) (ιC : ZC ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) C))
    (e : ZB ⟶ Z) (f : ZC ⟶ ZB)
    (hpb : IsPullback e (ιB ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hcomp : e ≫ ι = ιB ≫ ProjSpace.map A B n)
    (hpb' : IsPullback f (ιC ≫ ProjSpace.π C n) (ιB ≫ ProjSpace.π B n) (Spec.map (CommRingCat.ofHom (algebraMap B C))))
    (hcomp' : f ≫ ιB = ιC ≫ ProjSpace.map B C n) :
    IsPullback (f ≫ e) (ιC ≫ ProjSpace.π C n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A C))) ∧
    (f ≫ e) ≫ ι = ιC ≫ ProjSpace.map A C n :=
  P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_comp_and_comp_eq_map_of_isScalarTower.solution B C ι ιB ιC e f hpb hcomp hpb' hcomp'
