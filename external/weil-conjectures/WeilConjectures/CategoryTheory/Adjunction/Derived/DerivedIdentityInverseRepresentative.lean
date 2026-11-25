/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso

/-! # Inverse exact-derived identity comparison on cochain representatives -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
namespace CategoryTheory.Adjunction

/-- On a cochain representative, the inverse exact-derived identity comparison is the
localized inverse chain comparison followed by the inverse localization factor.
Source: the homotopy representative formula in `AdjunctionIdIso` and Mathlib localization.
(blueprint: lem-sf-derived-identity-inverse-representative)

Proof: compose on the right with the localization factor. Apply the existing homotopy
formula to the quotient of the cochain complex. The quotient comparison and the termwise
homotopy comparison are identity maps; remove them with functoriality and cancel the factor. -/
theorem mapDerivedCategoryNatIso_trans_idIso_inv_app_Q_obj {D : Type*} [Category D] [Abelian D]
    [HasDerivedCategory D] (R : D ⥤ D) [R.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits R]
    [CategoryTheory.Limits.PreservesFiniteColimits R]
    (r : R ≅ 𝟭 D) (P : CochainComplex D ℤ) :
    (Functor.mapDerivedCategoryNatIso (C := D) (D := D) (F := R) (G := 𝟭 D) r ≪≫
      Functor.mapDerivedCategoryIdIso D).inv.app
        (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex r.inv (.up ℤ)).app P) ≫
        (Functor.mapDerivedCategoryFactors (C₁ := D) (C₂ := D) R).inv.app P := by
  apply (Iso.eq_comp_inv ((Functor.mapDerivedCategoryFactors (C₁ := D) (C₂ := D) R).app P)).2
  have hh := Adjunction.mapDerivedCategoryNatIso_trans_idIso_inv_app_Qh_obj (C := D) (F := R) r
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  rw [Functor.mapDerivedCategoryFactorsh_hom_app] at hh
  erw [DerivedCategory.Qh.map_id, Category.comp_id] at hh
  have hh' : (Functor.mapDerivedCategoryNatIso (C := D) (D := D) (F := R) (G := 𝟭 D) r ≪≫
      Functor.mapDerivedCategoryIdIso D).inv.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      R.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso D).hom.app P) ≫
        (Functor.mapDerivedCategoryFactors (C₁ := D) (C₂ := D) R).hom.app P =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex r.inv (.up ℤ)).app P)) ≫
        (DerivedCategory.quotientCompQhIso D).hom.app _ := by
    have h := hh =≫ (DerivedCategory.quotientCompQhIso D).hom.app
      ((R.mapHomologicalComplex (.up ℤ)).obj P)
    simp only [Category.assoc, Iso.inv_hom_id_app] at h
    erw [Category.comp_id] at h
    exact h
  have hn := (Functor.mapDerivedCategoryNatIso (C := D) (D := D) (F := R) (G := 𝟭 D) r ≪≫
      Functor.mapDerivedCategoryIdIso D).inv.naturality
    ((DerivedCategory.quotientCompQhIso D).hom.app P)
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso D).hom.app P)]
  erw [reassoc_of% hn, hh', DerivedCategory.quotientCompQhIso_hom_naturality]
  rfl

end CategoryTheory.Adjunction
