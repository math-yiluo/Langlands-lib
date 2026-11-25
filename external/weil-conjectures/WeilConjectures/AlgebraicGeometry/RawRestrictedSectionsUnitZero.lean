/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RawRestrictedHomotopySectionsIso
import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison

/-! # Degree-zero normalization of the restricted sections unit

Source: Stacks Project, Cohomology on Sites, Tags 072W and 0BKV.
(blueprint: lem-sbc-raw-restricted-sections-unit-zero).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
/-- Transport the public bounded-below normalization to the unbounded unit. -/
private theorem unit_zero_comparison {C D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (M : C) :
    (DerivedCategory.homologyFunctor D 0).map
        (F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M)) ≫
      (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0).hom =
    (DerivedCategory.homologyFunctorFactors D 0).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M)) ≫
      HomologicalComplex.homologyMap
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).hom ≫
      F.toRightDerivedZero.app M := by
  have hu : F.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor C 0).obj M) ≫
      (F.rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj M)).inv =
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) := by
    apply (Iso.comp_inv_eq _).2
    have h := (Functor.rightDerivedNatTrans_app
        (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
        (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
        F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
        (HomotopyCategory.Plus.quasiIso C) (𝟙 _)
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M)).symm
    simp only [NatTrans.id_app, Category.id_comp] at h
    exact h
  dsimp only [Functor.homologyRightDerivedFunctorObjSingleFunctorIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  erw [← Functor.map_comp_assoc, hu]
  have h := F.rightDerivedPlusSingleUnitHomology_comp_comparison M
  dsimp only [Functor.rightDerivedPlusSingleUnitHomology,
    Functor.rightDerivedPlusSingleUnit,
    Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso,
    NatIso.ofComponents_hom_app] at h
  simp only [Functor.map_comp, Category.assoc] at h
  have he : (DerivedCategory.Plus.ι.preimageIso
      (X := (DerivedCategory.Plus.singleFunctor C 0).obj M)
      (Y := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor C 0).obj M))
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app M ≪≫
        (DerivedCategory.quotientCompQhIso C).symm.app _)).inv = 𝟙 _ := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.preimageIso_inv, Functor.map_preimage, Iso.trans_inv]
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  erw [he, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h
  let T := (F.mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M)
  let t := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M
  let e := (DerivedCategory.homologyFunctorFactors D 0).app T ≪≫
    (HomologicalComplex.homologyFunctor D (.up ℤ) 0).mapIso t ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)
  apply (cancel_epi e.inv).1
  have hp : e.inv =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app (F.obj M) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          (F.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 M).inv := by
    dsimp only [e, Iso.trans_inv, Functor.mapIso_inv]
    simp only [DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso,
      DerivedCategory.singleFunctorCompHomologyFunctorIso,
      HomologicalComplex.homologyFunctorSingleIso, Iso.trans_inv,
      CategoryTheory.Functor.isoWhiskerLeft_inv, Category.assoc,
      CategoryTheory.Functor.isoWhiskerRight_inv, Functor.mapIso_inv,
      SingleFunctors.evaluation_map, NatTrans.comp_app, NatIso.ofComponents_inv_app,
      CategoryTheory.Functor.whiskerLeft_app, CategoryTheory.Functor.associator_inv_app,
      CategoryTheory.Functor.whiskerRight_app, Category.id_comp,
      Functor.mapHomotopyCategoryPlusSingleFunctorQhObjIso,
      Functor.preimageIso_inv]
    rw [DerivedCategory.singleFunctorsPostcompQIso_inv_hom]
    simp only [NatTrans.id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    dsimp only [DerivedCategory.Plus.homologyFunctor,
      CategoryTheory.Functor.comp_map]
    rw [CategoryTheory.Functor.map_preimage]
    have hq (K : CochainComplex D ℤ) :
        (DerivedCategory.quotientCompQhIso D).inv.app K = 𝟙 _ := by
      rfl
    change _ = (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
      (DerivedCategory.homologyFunctorFactors D 0).inv.app _ ≫
      (DerivedCategory.homologyFunctor D 0).map
        (DerivedCategory.Q.map t.inv ≫ (DerivedCategory.quotientCompQhIso D).inv.app T)
    rw [hq]
    erw [Category.comp_id]
    have hn := (DerivedCategory.homologyFunctorFactors D 0).inv.naturality t.inv
    dsimp only [CategoryTheory.Functor.comp_map] at hn
    exact congrArg (_ ≫ ·) hn
  have heh : e.hom =
      (DerivedCategory.homologyFunctorFactors D 0).hom.app T ≫
        HomologicalComplex.homologyMap t.hom 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).hom := by
    rfl
  erw [← reassoc_of% heh]
  rw [Iso.inv_hom_id_assoc, hp, Category.assoc]
  exact h

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

/-- The derived-sections unit transported through the localization comparisons.
Source: Stacks Project, Tags 072W and 0BKV.
(blueprint: lem-sbc-raw-restricted-sections-unit-zero). -/
noncomputable def sectionsUnit {Y : Scheme.{v}} (W : Y.Etale)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :
    DerivedCategory.Q.obj (((underivedSections W).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.obj
        ((upperStar AddCommGrpCat.{v + 1} W.hom).mapDerivedCategory.obj
          (DerivedCategory.Q.obj K)) :=
  let L := upperStar AddCommGrpCat.{v + 1} W.hom
  let R := Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}
  let LK := (L.mapHomologicalComplex (.up ℤ)).obj K
  (DerivedCategory.quotientCompQhIso _).inv.app
      ((R.mapHomologicalComplex (.up ℤ)).obj LK) ≫
    R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj LK) ≫
    R.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app LK) ≫
    R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.inv.app K)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Normalize the unit for exact restriction followed by any left-exact sections functor. -/
private theorem restricted_unit_zero {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.EnoughInjectives D] [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : D ⥤ AddCommGrpCat.{v + 1}) [R.Additive] [PreservesFiniteLimits R] (A : C) :
    let K := (CochainComplex.singleFunctor C 0).obj A
    let LK := (L.mapHomologicalComplex (.up ℤ)).obj K
    let η := (DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
        ((R.mapHomologicalComplex (.up ℤ)).obj LK) ≫
      R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient D (.up ℤ)).obj LK) ≫
      R.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso D).hom.app LK) ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.inv.app K)
    let σ := (HomologicalComplex.homologyFunctor _ _ 0).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (L ⋙ R) (.up ℤ) 0).app A) ≪≫
      HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 _
    σ.inv ≫ (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} 0).inv.app
        (((L ⋙ R).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map η =
      (Evaluation.zeroIso L R A).inv := by
  intro K LK η σ
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
  let s := (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app A
  have ht : η ≫ R.rightDerivedFunctor.map
      ((L.mapDerivedCategorySingleFunctor 0).hom.app A) =
      DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map s) ≫
        R.rightDerivedFunctorUnit.app ((HomotopyCategory.singleFunctor _ 0).obj
          (L.obj A)) := by
    have hn := R.rightDerivedFunctorUnit.naturality
      ((HomotopyCategory.quotient _ (.up ℤ)).map s)
    dsimp only [Functor.comp_map] at hn
    have hq₁ : (DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
        ((R.mapHomologicalComplex (.up ℤ)).obj ((L.mapHomologicalComplex (.up ℤ)).obj K)) =
        𝟙 _ := rfl
    have hq₂ : (DerivedCategory.quotientCompQhIso _).hom.app
        ((L.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
    dsimp only [η]
    rw [hq₁, hq₂]
    simp only [Category.assoc]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
    change R.rightDerivedFunctorUnit.app _ ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.inv.app K) ≫
      R.rightDerivedFunctor.map ((L.mapDerivedCategorySingleFunctor 0).hom.app A) = _
    rw [← CategoryTheory.Functor.map_comp]
    have hf := L.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app A
    change L.mapDerivedCategoryFactors.inv.app K ≫
      (L.mapDerivedCategorySingleFunctor 0).hom.app A = DerivedCategory.Q.map s at hf
    rw [hf]
    change R.rightDerivedFunctorUnit.app _ ≫
      R.rightDerivedFunctor.map (DerivedCategory.Q.map s) = _
    exact hn.symm
  apply (cancel_mono (Evaluation.zeroIso L R A).hom).1
  rw [Iso.inv_hom_id]
  dsimp only [Evaluation.zeroIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [DerivedCategory.Plus.singleFunctorιIso,
    Iso.app_hom, Iso.refl_hom, NatTrans.id_app,
    Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  change σ.inv ≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} 0).inv.app
      (((L ⋙ R).mapHomologicalComplex (.up ℤ)).obj K) ≫
    H.map η ≫
    H.map (R.rightDerivedFunctor.map ((L.mapDerivedCategorySingleFunctor 0).hom.app A)) ≫
    (R.homologyRightDerivedFunctorObjSingleFunctorIso (L.obj A) 0).hom ≫
    (R.rightDerivedZeroIsoSelf.app (L.obj A)).hom = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp_assoc, ht, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  have h := unit_zero_comparison R (L.obj A)
  erw [reassoc_of% h]
  have hn := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} 0).inv.naturality
    ((R.mapHomologicalComplex (.up ℤ)).map s)
  dsimp only [CategoryTheory.Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  erw [(DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} 0).inv_hom_id_app_assoc]
  let t := (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app (L.obj A)
  let u := (HomologicalComplex.singleMapHomologicalComplex (L ⋙ R) (.up ℤ) 0).app A
  have hs : (R.mapHomologicalComplex (.up ℤ)).map s ≫ t.hom = u.hom := by
    ext n : 1
    by_cases hn : n = 0
    · subst n
      change R.map (𝟙 (L.obj A)) ≫ 𝟙 _ = 𝟙 _
      simp
    · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn).eq_of_tgt _ _
  have hs' : (R.mapHomologicalComplex (.up ℤ)).map s = u.hom ≫ t.inv :=
    (Iso.eq_comp_inv t).2 hs
  rw [hs', CategoryTheory.Functor.map_comp]
  dsimp only [σ, Iso.trans_inv, CategoryTheory.Functor.mapIso_inv,
    HomologicalComplex.homologyFunctor_map]
  change (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (R.obj (L.obj A))).inv ≫
    HomologicalComplex.homologyMap u.inv 0 ≫
    HomologicalComplex.homologyMap u.hom 0 ≫
    HomologicalComplex.homologyMap t.inv 0 ≫
    HomologicalComplex.homologyMap t.hom 0 ≫
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (R.obj (L.obj A))).hom ≫
    R.toRightDerivedZero.app (L.obj A) ≫
    (R.rightDerivedZeroIsoSelf.app (L.obj A)).hom = 𝟙 _
  erw [← HomologicalComplex.homologyMap_comp_assoc, u.inv_hom_id]
  simp only [HomologicalComplex.homologyMap_id, Category.id_comp]
  erw [← HomologicalComplex.homologyMap_comp_assoc, t.inv_hom_id]
  simp only [HomologicalComplex.homologyMap_id, Category.id_comp]
  erw [CategoryTheory.Functor.rightDerivedZeroIsoSelf_inv_hom_id_app]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On a single sheaf the homology of the transported unit is the inverse of
`zeroIso`, after identifying single-complex homology with underived sections.
Source: Stacks Project, Tags 072W and 0BKV (degree-zero derived sections).
(blueprint: lem-sbc-raw-restricted-sections-unit-zero).

Proof: expand `zeroIso` into the exact-restriction single comparison, the
unbounded-to-bounded-below derived comparison, the injective-resolution homology
comparison, and the classical degree-zero comparison. The compatibility of the
two derived functors with their units, given by `Functor.rightDerivedNatTrans_app`,
cancels the unbounded-to-bounded-below comparison. Apply the proved
`Functor.rightDerivedPlusSingleUnitHomology_comp_comparison` to the restricted
sheaf: it identifies the bounded-below single unit with `toRightDerivedZero`.
Since sections preserve finite limits, `rightDerivedZeroIsoSelf` is its inverse.
Thus the classical comparison cancels the same augmentation. The single-complex
homology isomorphism identifies its source with the sheaf of sections. Naturality
of exact restriction's single-complex comparison and homology's localization
comparison gives the
displayed equality. This argument requires no K-injectivity of the single
sheaf, and includes the zero sheaf and the empty etale object. -/
theorem sectionsUnit_zero {Y : Scheme.{v}} (W : Y.Etale)
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (underivedSingleIso W A).inv ≫
        ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} 0).app
          (((underivedSections W).mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor _ 0).obj A))).inv ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
          (sectionsUnit W ((CochainComplex.singleFunctor _ 0).obj A)) =
      (zeroIso W A).inv := by
  exact restricted_unit_zero
    (upperStar AddCommGrpCat.{v + 1} W.hom)
    (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}) A

end AlgebraicGeometry.Etale.RawRestrictedComparison
