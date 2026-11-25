/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! # Cancelling an equivalence after exact localization

Source: Stacks 015F; finite coefficient realization in prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-derived-equivalence-cancellation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local implicit_reducible] Equivalence.mapDerivedCategory

section
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

private theorem derived_counit_factors (R : C ≌ D)
    [R.functor.Additive] [R.inverse.Additive] (K : CochainComplex D ℤ) :
    R.functor.mapDerivedCategory.map (R.inverse.mapDerivedCategoryFactors.hom.app K) ≫
      R.functor.mapDerivedCategoryFactors.hom.app
        ((R.inverse.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex R.counitIso.hom (.up ℤ)).app K) =
    R.mapDerivedCategory.counitIso.hom.app (DerivedCategory.Q.obj K) := by
  change _ = (Functor.mapDerivedCategoryCompIso R.inverse R.functor).hom.app _ ≫
    (Functor.mapDerivedCategoryNatIso R.counitIso).hom.app _ ≫
    (Functor.mapDerivedCategoryIdIso D).hom.app _
  have hid : (Functor.mapDerivedCategoryIdIso D).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 D).mapDerivedCategoryFactors.hom.app K := by
    have h := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj D
      ((HomotopyCategory.quotient D (.up ℤ)).obj K)
    have hn := (Functor.mapDerivedCategoryIdIso D).hom.naturality
      ((DerivedCategory.quotientCompQhIso D).hom.app K)
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hn
    conv_rhs at hn => rw [h]
    rw [Functor.mapDerivedCategoryFactorsh_hom_app] at hn
    simp only [Category.assoc] at hn
    apply (cancel_epi ((𝟭 D).mapDerivedCategory.map
      ((DerivedCategory.quotientCompQhIso D).hom.app K))).mp
    rw [hn]
    congr 1
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift]
    repeat erw [Functor.map_id]
    erw [Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  rw [hid, Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem derived_unitInv_factors (R : C ≌ D)
    [R.functor.Additive] [R.inverse.Additive] (K : CochainComplex C ℤ) :
    R.inverse.mapDerivedCategory.map (R.functor.mapDerivedCategoryFactors.hom.app K) ≫
      R.inverse.mapDerivedCategoryFactors.hom.app
        ((R.functor.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex R.unitIso.inv (.up ℤ)).app K) =
    R.mapDerivedCategory.unitIso.inv.app (DerivedCategory.Q.obj K) := by
  apply R.mapDerivedCategory.functor.map_injective
  apply (cancel_mono (R.functor.mapDerivedCategoryFactors.hom.app K)).mp
  rw [← R.mapDerivedCategory.counit_app_functor]
  simp only [Functor.map_comp, Category.assoc]
  erw [R.functor.mapDerivedCategoryFactors_hom_naturality]
  have ht : (R.functor.mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex R.unitIso.inv (.up ℤ)).app K) =
      (NatTrans.mapHomologicalComplex R.counitIso.hom (.up ℤ)).app
        ((R.functor.mapHomologicalComplex (.up ℤ)).obj K) := by
    ext i
    exact (R.counit_app_functor (K.X i)).symm
  rw [ht]
  erw [Category.assoc, Category.assoc,
    derived_counit_factors R ((R.functor.mapHomologicalComplex (.up ℤ)).obj K)]
  have hn := R.mapDerivedCategory.counitIso.hom.naturality
    (R.functor.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  convert hn using 1 <;>
    simp only [Equivalence.mapDerivedCategory, Equivalence.mk, Iso.trans_hom,
      NatTrans.comp_app, Functor.comp_obj, Functor.id_obj, Category.assoc]
end

section
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (H : A ⥤ B) (L : B ⥤ C) (R : C ≌ D) (P : A ⥤ D)
  [H.Additive] [L.Additive] [R.functor.Additive] [R.inverse.Additive] [P.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- Exact localization commutes with cancelling the unit of an equivalence.

Source: Stacks 015F and the equivalence cancellation in the finite coefficient
realization of prop-sf-pf-coherence.proof.md.
(blueprint: lem-sf-derived-equivalence-cancellation).

Proof: the counit of the derived equivalence is the localized ordinary counit
with its composition factors. Apply the faithful forward equivalence and its
triangle identity to obtain the analogous inverse-unit factorization. Equality
of natural transformations on a derived category is detected on localized
cochain complexes. On such a complex, postcompose both sides with the invertible
factors for H and L. Naturality moves the derived unit to the resulting complex;
its factorization cancels the forward-equivalence factor. The composition and
natural-isomorphism factorization equations leave the localization of the
ordinary cancellation word on both sides, degree by degree. Cancel the factors.
This argument includes zero objects and empty categories whenever the displayed
category and equivalence data exist. -/
theorem mapDerivedCategory_cancelEquivalence (q : P ≅ H ⋙ L ⋙ R.functor) :
    let δ := Functor.isoWhiskerRight q R.inverse ≪≫
      Functor.isoWhiskerLeft H (Functor.isoWhiskerLeft L R.unitIso.symm) ≪≫
      Functor.isoWhiskerLeft H (Functor.rightUnitor L)
    let o := (Functor.mapDerivedCategoryCompIso H (L ⋙ R.functor)).symm ≪≫
      Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso L R.functor).symm
    (Functor.mapDerivedCategorySquareIso δ).hom =
      Functor.whiskerRight ((Functor.mapDerivedCategoryNatIso q).hom ≫ o.hom)
        R.inverse.mapDerivedCategory ≫
      Functor.whiskerLeft (H.mapDerivedCategory ⋙ L.mapDerivedCategory)
        R.mapDerivedCategory.unitIso.inv := by
  dsimp only
  let δ := Functor.isoWhiskerRight q R.inverse ≪≫
    Functor.isoWhiskerLeft H (Functor.isoWhiskerLeft L R.unitIso.symm) ≪≫
    Functor.isoWhiskerLeft H (Functor.rightUnitor L)
  let o := (Functor.mapDerivedCategoryCompIso H (L ⋙ R.functor)).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso L R.functor).symm
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  let T := (L.mapHomologicalComplex (.up ℤ)).obj ((H.mapHomologicalComplex (.up ℤ)).obj K)
  let a := L.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
    L.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K)
  apply (cancel_mono a).mp
  have ho : o.hom.app (DerivedCategory.Q.obj K) ≫
      R.functor.mapDerivedCategory.map a ≫
      R.functor.mapDerivedCategoryFactors.hom.app T =
      (H ⋙ L ⋙ R.functor).mapDerivedCategoryFactors.hom.app K := by
    dsimp only [o, a, T, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    simp only [Functor.map_comp, Category.assoc]
    erw [← (Functor.mapDerivedCategoryCompIso L R.functor).inv.naturality_assoc]
    erw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
      Functor.mapDerivedCategoryCompIso_hom_app_factors]
  have hh : (Functor.mapDerivedCategoryNatIso q).hom.app (DerivedCategory.Q.obj K) ≫
      o.hom.app (DerivedCategory.Q.obj K) ≫ R.functor.mapDerivedCategory.map a =
      P.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex q.hom (.up ℤ)).app K) ≫
        R.functor.mapDerivedCategoryFactors.inv.app T := by
    apply (cancel_mono (R.functor.mapDerivedCategoryFactors.hom.app T)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [ho, Functor.mapDerivedCategoryNatIso_fac]
    erw [Category.comp_id]
  rw [Functor.exactSquare_fac δ K]
  have hu := R.mapDerivedCategory.unitIso.inv.naturality a
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hu ⊢
  rw [Category.assoc, ← hu]
  erw [← R.inverse.mapDerivedCategory.map_comp_assoc]
  simp only [Category.assoc]
  erw [hh]
  rw [← derived_unitInv_factors R T]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← R.inverse.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  erw [R.inverse.mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [← DerivedCategory.Q.map_comp]
  congr 2
  congr 1
  ext i
  simp only [δ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  erw [Category.comp_id]
  rfl
end

end CategoryTheory.Functor
