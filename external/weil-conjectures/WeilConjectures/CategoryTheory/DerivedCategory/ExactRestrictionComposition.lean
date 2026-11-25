/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Composition of the inverse factorization comparisons of exact functors

Source: functoriality of ordinary unbounded localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (S : C ⥤ B) (R : B ⥤ A) (U : C ⥤ A)
  [S.Additive] [R.Additive] [U.Additive]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

/-- The comparison of successive exact restrictions with an isomorphic exact restriction.
Source: localization functoriality
(auxiliary; not a blueprint node). -/
def exactDerivedRestrictionComposition (η : S ⋙ R ≅ U) :
    S.mapDerivedCategory ⋙ R.mapDerivedCategory ≅ U.mapDerivedCategory :=
  mapDerivedCategoryCompIso S R ≪≫ mapDerivedCategoryNatIso η

/-- Inverse localization comparisons respect composition of exact restrictions.
Source: localization functoriality
(auxiliary; not a blueprint node).
Proof: cancel the factorization for U. The defining factorization equations for the
composition isomorphism and the image of η reduce the result to cancellation of the
two inverse factorization isomorphisms. -/
theorem exactDerivedRestrictionComposition_inv_factors (η : S ⋙ R ≅ U)
    (K : CochainComplex C ℤ) :
    R.mapDerivedCategoryFactors.inv.app ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
      R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.inv.app K) ≫
      (exactDerivedRestrictionComposition S R U η).hom.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex η (.up ℤ)).hom.app K) ≫
      U.mapDerivedCategoryFactors.inv.app K := by
  have hi : (mapDerivedCategoryCompIso S R).hom.app (DerivedCategory.Q.obj K) ≫
      (S ⋙ R).mapDerivedCategoryFactors.hom.app K =
    R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (cancel_epi ((mapDerivedCategoryCompIso S R).inv.app
      (DerivedCategory.Q.obj K))).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact (mapDerivedCategoryCompIso_hom_app_factors S R K).symm
  apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app K)).mp
  simp only [exactDerivedRestrictionComposition, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryNatIso_fac, ← Category.assoc _ _
    (DerivedCategory.Q.map _), hi]
  simp only [Category.assoc, ← R.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  dsimp only [comp_obj]
  rw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc, Category.comp_id]
  rfl

/-- The forward composition comparison commutes with localization factorizations.
Source: localization functoriality
(auxiliary; not a blueprint node).
Proof: expand the comparison, use natural-isomorphism factorization, and cancel the
exact-functor compositor against its inverse. -/
theorem exactDerivedRestrictionComposition_hom_factors (η : S ⋙ R ≅ U)
    (K : CochainComplex C ℤ) :
    (exactDerivedRestrictionComposition S R U η).hom.app (DerivedCategory.Q.obj K) ≫
        U.mapDerivedCategoryFactors.hom.app K =
      R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex η (.up ℤ)).hom.app K) := by
  simp only [exactDerivedRestrictionComposition, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((mapDerivedCategoryCompIso S R).inv.app
    (DerivedCategory.Q.obj K))).1
  rw [Iso.inv_hom_id_app_assoc, mapDerivedCategoryCompIso_hom_app_factors_assoc S R K]
  rfl

end CategoryTheory.Functor
