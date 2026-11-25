/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction

/-!
# The base change map of the forgetful functor along a lifted adjunction

For an adjunction `adj : L ⊣ R` lifted to algebras with invertible structure morphism
(`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`), the forgetful functors commute
strictly with the left adjoints (`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso`),
and the mate of this identification, the base change map
`mapOfNatIso eR ⋙ forget F ⟶ forget G ⋙ R`, is the identity; in particular it is an isomorphism
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_mateEquiv_mapOfNatIsoCompForgetIso_inv`).
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ C} {G : D ⥤ D}
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
  (h : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)) = eR.hom)

/-- The base change map of the forgetful functors along the lifted adjunction
`mapOfNatIsoAdjunction adj eL eR h` and `adj`, the mate of the identification
`forget F ⋙ L ≅ mapOfNatIso eL ⋙ forget G`, is the identity of the underlying objects. -/
lemma mateEquiv_mapOfNatIsoCompForgetIso_inv_app (M : IsoAlgebra G) :
    (mateEquiv (mapOfNatIsoAdjunction adj eL eR h) adj
      (mapOfNatIsoCompForgetIso eL).inv).app M = 𝟙 _ := by
  simp [mateEquiv_apply, mapOfNatIsoCompForgetIso]

/-- The base change map of the forgetful functors along the lifted adjunction
`mapOfNatIsoAdjunction adj eL eR h` and `adj` is an isomorphism. -/
instance isIso_mateEquiv_mapOfNatIsoCompForgetIso_inv :
    IsIso (mateEquiv (mapOfNatIsoAdjunction adj eL eR h) adj
      (mapOfNatIsoCompForgetIso eL).inv) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [mateEquiv_mapOfNatIsoCompForgetIso_inv_app]
  infer_instance

end CategoryTheory.Endofunctor.IsoAlgebra
