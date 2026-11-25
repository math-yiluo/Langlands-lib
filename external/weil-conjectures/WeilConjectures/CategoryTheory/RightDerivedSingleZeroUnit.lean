/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison

/-! # The right-derived unit on a single object

Source: Stacks Project, Tag 0156, and the injective-resolution definition of derived functors.
(blueprint: lem-sbc-right-derived-single-zero-unit).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  [HasKInjectiveResolutions C]

/-- The localization unit on a single object, with its source and target expressed
using the single functors. It is an actual composite of the existing comparisons.
Source: Stacks Project, Tag 0156, Section 13.20; `rightDerivedFunctorUnit` and
`mapCochainComplexSingleFunctor` give the localization unit and single comparison.
(blueprint: lem-sbc-right-derived-single-zero-unit). -/
noncomputable def rightDerivedSingleUnit (F : C ⥤ D) [F.Additive] (M : C) :
    (DerivedCategory.singleFunctor D 0).obj (F.obj M) ⟶
      F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M) :=
  DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app M) ≫
    cast (by rfl) (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Abelian in
/-- Transport the proved bounded-below single-unit normalization to the unbounded unit. -/
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


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The right-derived unit induces the inverse of the canonical zeroth comparison.
Source: Stacks Project, Tag 0156; the augmentation of an injective resolution and
Mathlib's definition of `toRightDerivedZero`.
(blueprint: lem-sbc-right-derived-single-zero-unit).

Proof: Choose the injective resolution I of M used in the single comparison.
The localization unit is represented by F applied to the augmentation M[0] → I.
The bounded-below/unbounded compatibility carries this unit to the same map,
by its defining equality with the two right-derived units. On zeroth homology,
the augmentation is precisely toRightDerivedZero: this follows by the description
of the kernel of F(I⁰) → F(I¹). The single homology comparison identifies the
source with F(M). The single right-derived homology comparison identifies the
target with R⁰F(M). Finally rightDerivedZeroIsoSelf is the inverse of
 toRightDerivedZero for a left exact F. Their composite is the identity of F(M),
which proves the formula. This uses no exactness beyond left exactness of F;
zero objects and the zero functor give the same identity. -/
theorem rightDerivedSingleUnit_zero (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (M : C) :
    (DerivedCategory.homologyFunctor D 0).map (F.rightDerivedSingleUnit M) ≫
      (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
        F.rightDerivedZeroIsoSelf.app M).hom =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).hom.app (F.obj M)  := by
  let t := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M
  dsimp only [rightDerivedSingleUnit, Iso.trans_hom]
  rw [Functor.map_comp, Category.assoc]
  have hu := unit_zero_comparison F M
  erw [reassoc_of% hu]
  have hn := (DerivedCategory.homologyFunctorFactors D 0).hom.naturality t.inv
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← HomologicalComplex.homologyMap_comp_assoc, t.inv_hom_id]
  erw [HomologicalComplex.homologyMap_id, Category.id_comp]
  erw [F.rightDerivedZeroIsoSelf_inv_hom_id_app]
  simp only [Category.comp_id]
  simp only [DerivedCategory.Q_obj_single_obj, HomologicalComplex.homologyFunctor_obj,
    DerivedCategory.singleFunctorCompHomologyFunctorIso, SingleFunctors.evaluation_obj,
    SingleFunctors.postcomp_functor, Iso.trans_hom, isoWhiskerRight_hom, mapIso_hom,
    SingleFunctors.evaluation_map, DerivedCategory.singleFunctorsPostcompQIso_hom_hom,
    whiskerRight_id', isoWhiskerLeft_hom, Category.id_comp, NatTrans.comp_app, comp_obj,
    id_obj, associator_hom_app, whiskerLeft_app,
    HomologicalComplex.homologyFunctorSingleIso_hom_app]

end CategoryTheory.Functor
