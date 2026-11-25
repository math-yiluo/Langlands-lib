/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import Mathlib.AlgebraicGeometry.AffineScheme

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

/-- The exact derived identity comparison on a cochain representative.
Source: functoriality of localization
(blueprint: lem-pur-exact-restriction-composition).
Proof: use the homotopy representative formula, and identify the two factorization
components through the quotient-to-derived comparison, whose components are identities. -/
theorem mapDerivedCategoryIdIso_hom_app_Q_obj (K : CochainComplex A ℤ) :
    (mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app K := by
  rw [mapDerivedCategoryIdIso_hom_app]
  have h : (mapHomologicalComplexIdIso A (.up ℤ)).hom.app K = 𝟙 _ := rfl
  rw [h]
  erw [DerivedCategory.Q.map_id, Category.comp_id]

/-- The derived comparison of an exact restriction identified with the identity.
Source: localization functoriality
(blueprint: lem-pur-exact-restriction-composition). -/
def exactDerivedRestrictionUnit (R : A ⥤ A) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (η : R ≅ 𝟭 A) :
    R.mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
  mapDerivedCategoryNatIso η ≪≫ mapDerivedCategoryIdIso A

/-- The inverse factorization formula for an identity restriction.
Source: localization functoriality
(blueprint: lem-pur-exact-restriction-composition).
Proof: use the natural-isomorphism factorization equation and the cochain formula for
the derived identity. The factorization and its inverse cancel. -/
theorem exactDerivedRestrictionUnit_inv_factors (R : A ⥤ A) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (η : R ≅ 𝟭 A)
    (K : CochainComplex A ℤ) :
    R.mapDerivedCategoryFactors.inv.app K ≫
      (exactDerivedRestrictionUnit R η).hom.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map (((NatIso.mapHomologicalComplex η (.up ℤ)) ≪≫
      Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app K) := by
  simp only [exactDerivedRestrictionUnit, Iso.trans_hom, NatTrans.comp_app]
  rw [mapDerivedCategoryIdIso_hom_app_Q_obj, mapDerivedCategoryNatIso_fac,
    Iso.inv_hom_id_app_assoc]
  congr 1
  apply HomologicalComplex.hom_ext
  intro i
  simp only [NatTrans.mapHomologicalComplex_app_f, id_obj, HomologicalComplex.comp_f,
    NatIso.mapHomologicalComplex_hom_app_f, mapHomologicalComplexIdIso_hom_app_f]
  exact (Category.comp_id _).symm

/-- The inverse unit comparison commutes with the forward localization factorization.
Source: functoriality of localization
(blueprint: lem-pur-exact-restriction-composition).
Proof: cancel the invertible localized ordinary unit. The inverse-factor equation
and both isomorphism inverse laws reduce each composite to the identity. -/
theorem exactDerivedRestrictionUnit_inv_fac (R : A ⥤ A) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (η : R ≅ 𝟭 A)
    (K : CochainComplex A ℤ) :
    (exactDerivedRestrictionUnit R η).inv.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategoryFactors.hom.app K =
      DerivedCategory.Q.map (((NatIso.mapHomologicalComplex η (.up ℤ)) ≪≫
        Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app K) := by
  let ηc := NatIso.mapHomologicalComplex η (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso A (.up ℤ)
  apply (cancel_mono (DerivedCategory.Q.map (ηc.hom.app K))).1
  rw [← exactDerivedRestrictionUnit_inv_factors R η K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  rw [exactDerivedRestrictionUnit_inv_factors R η K,
    ← DerivedCategory.Q.map_comp, ηc.inv_hom_id_app, DerivedCategory.Q.map_id]
  rfl

end CategoryTheory.Functor
