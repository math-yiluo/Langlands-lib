/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# The derived square of an inverse isomorphism

The isomorphism `D(P) ⋙ D(Q) ≅ D(R) ⋙ D(S)` induced on derived categories by the inverse of
an isomorphism `e : P ⋙ Q ≅ R ⋙ S` of exact functors is the inverse of the one induced by `e`
(`CategoryTheory.Functor.mapDerivedCategorySquareIso_symm`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory F]
  {P : C ⥤ D} {Q : D ⥤ F} {R : C ⥤ E} {S : E ⥤ F}
  [P.Additive] [Q.Additive] [R.Additive] [S.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- The derived square of the inverse of `e : P ⋙ Q ≅ R ⋙ S` is the inverse of the derived
square of `e`. -/
lemma mapDerivedCategorySquareIso_symm (e : P ⋙ Q ≅ R ⋙ S) :
    mapDerivedCategorySquareIso e.symm = (mapDerivedCategorySquareIso e).symm := by
  apply Iso.ext
  simp only [mapDerivedCategorySquareIso, mapDerivedCategoryNatIso_symm, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Category.assoc]

end CategoryTheory.Functor
