/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison

/-! # The degree-zero unit of a derived adjunction

Source: Stacks Project, Tag 0GJU, degree-zero unit identification.
(blueprint: lem-weil-pbc-derived-adjunction-single-zero).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

omit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_single_complex (M : C) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app
          ((CochainComplex.singleFunctor C 0).obj M) ≫
        (R.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app M) ≫
        (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app (L.obj M) =
      (CochainComplex.singleFunctor C 0).map (adj.unit.app M) := by
  ext i
  by_cases hi : i = 0
  · subst i
    simp only [HomologicalComplex.comp_f, mapHomologicalComplex_unit_app_f,
      Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    change adj.unit.app _ ≫ R.map
      (L.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (L.obj M)).inv) ≫
      (R.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (L.obj M)).hom ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (R.obj (L.obj M))).inv) =
      ((HomologicalComplex.single C (.up ℤ) 0).map (adj.unit.app M)).f 0
    rw [HomologicalComplex.single_map_f_self]
    simp only [Functor.map_comp, Category.assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    simpa only [Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj] using
      (adj.unit.naturality_assoc
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (R.obj (L.obj M))).inv).symm
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi).eq_of_src _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_single (M : C) :
    adj.derivedPlus.unit.app ((DerivedCategory.Plus.singleFunctor C 0).obj M) ≫
        R.rightDerivedFunctorPlus.map
          ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app M) =
      (DerivedCategory.Plus.singleFunctor C 0).map (adj.unit.app M) ≫
        R.rightDerivedPlusSingleUnit (L.obj M) := by
  have h := adj.derivedPlus_unit_app_fac ((HomotopyCategory.Plus.singleFunctor C 0).obj M)
  have hL : (L.mapDerivedCategoryPlusSingleFunctor 0).hom.app M =
      L.mapDerivedCategoryPlusFactorsh.hom.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M) ≫
        (L.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 M).hom := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.map_comp, Functor.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app,
      Functor.mapHomotopyCategoryPlusSingleFunctorQhObjIso, Functor.preimageIso_hom,
      Functor.map_preimage]
    change _ = L.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M)) ≫ _
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    simp only [HomotopyCategory.quotient_obj_singleFunctors_obj, Functor.comp_obj,
      Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ,
      Functor.isoWhiskerRight_refl, Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans,
      Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Iso.refl_hom, NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj, Functor.whiskerRight_app,
      NatTrans.id_app, Category.comp_id, Category.id_comp, Functor.mapHomotopyCategory_obj,
      DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
      Quotient.lift.isLift_hom, Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors,
      Functor.map_id, ObjectProperty.ι_obj, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    erw [Functor.map_id, Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
  rw [hL, Functor.map_comp, ← Category.assoc]
  erw [h]
  let u : L.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor C 0).obj M) ≅
      (HomotopyCategory.Plus.singleFunctor D 0).obj (L.obj M) :=
    (HomotopyCategory.Plus.ι D).preimageIso
      ((HomotopyCategory.quotient D (.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app M))
  have hu : DerivedCategory.Plus.Qh.map u.hom =
      (L.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 M).hom := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [u, Functor.preimageIso_hom, Functor.map_preimage,
      Functor.mapHomotopyCategoryPlusSingleFunctorQhObjIso]
    change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι D).map
      ((HomotopyCategory.Plus.ι D).preimage _)) = _
    rw [Functor.map_preimage]
    change _ = 𝟙 _ ≫ _
    exact (Category.id_comp _).symm
  rw [← hu, Category.assoc]
  have hn := R.rightDerivedFunctorPlusUnith.naturality u.hom
  dsimp only [Functor.comp_map] at hn
  erw [← hn]
  have he : (DerivedCategory.Plus.ι.preimageIso
      (X := (DerivedCategory.Plus.singleFunctor D 0).obj (L.obj M))
      (Y := DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.singleFunctor D 0).obj (L.obj M)))
      ((DerivedCategory.singleFunctorIsoCompQ D 0).app (L.obj M) ≪≫
        (DerivedCategory.quotientCompQhIso D).symm.app _)).inv = 𝟙 _ := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.preimageIso_inv, Functor.map_preimage, Iso.trans_inv]
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  simp only [Functor.rightDerivedPlusSingleUnit, he, Functor.map_id]
  suffices hp : DerivedCategory.Plus.Qh.map
        (adj.mapHomotopyCategoryPlus.unit.app
          ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) ≫
      DerivedCategory.Plus.Qh.map (R.mapHomotopyCategoryPlus.map u.hom) =
      (DerivedCategory.Plus.singleFunctor C 0).map (adj.unit.app M) ≫
        (R.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (L.obj M)).inv by
    erw [Category.comp_id]
    simpa only [Category.assoc] using congrArg (fun a ↦ a ≫
      R.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor D 0).obj (L.obj M))) hp
  apply (cancel_mono
    (R.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (L.obj M)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, Functor.mapHomotopyCategoryPlusSingleFunctorQhObjIso,
    Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  erw [Category.id_comp]
  change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι C).map
      (adj.mapHomotopyCategoryPlus.unit.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M))) ≫
    DerivedCategory.Qh.map ((R.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.Plus.ι D).map u.hom)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app (L.obj M)) =
    DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map (adj.unit.app M))
  rw [ι_map_mapHomotopyCategoryPlus_unit_app]
  erw [mapHomotopyCategory_unit_app_quotient (.up ℤ) adj
    ((CochainComplex.singleFunctor C 0).obj M)]
  dsimp only [u, Functor.preimageIso_hom]
  rw [Functor.map_preimage]
  simp only [Functor.mapIso_hom]
  rw [Functor.mapHomotopyCategory_map]
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫
    DerivedCategory.Q.map _ = DerivedCategory.Q.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (unit_single_complex adj M)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Degree-zero homology of the actual derived adjunction unit is the ordinary unit.
Source: Stacks Project, Tag 0GJU, degree-zero identification; Tag 05TD, derived functors.
(blueprint: lem-weil-pbc-derived-adjunction-single-zero).

Proof: on a single complex the derived-unit factorization and naturality of the
right-derived unit identify the map with the ordinary unit followed by the
right-derived-functor single unit. This follows degreewise from the ordinary adjunction
unit and the single-complex comparisons. Apply degree-zero homology. The proved
single-unit homology comparison identifies the second map with toRightDerivedZero.
This is invertible for a left exact right adjoint, giving the asserted target
isomorphism. Naturality of single-complex homology gives the displayed equality. -/
theorem derivedPlus_unit_homology_zero [PreservesFiniteLimits R] (M : C) :
    ∃ e : (DerivedCategory.Plus.homologyFunctor C 0).obj
          ((L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus).obj
            ((DerivedCategory.Plus.singleFunctor C 0).obj M)) ≅ R.obj (L.obj M),
      (DerivedCategory.Plus.homologyFunctor C 0).map
          (adj.derivedPlus.unit.app ((DerivedCategory.Plus.singleFunctor C 0).obj M)) ≫
        e.hom =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).hom.app M ≫
        adj.unit.app M := by
  let H := DerivedCategory.Plus.homologyFunctor C 0
  let c := DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := C) 0
  let d := R.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0
  let e := H.mapIso (R.rightDerivedFunctorPlus.mapIso
      ((L.mapDerivedCategoryPlusSingleFunctor 0).app M)) ≪≫
    d.app (L.obj M) ≪≫ (asIso (R.toRightDerivedZero.app (L.obj M))).symm
  refine ⟨e, ?_⟩
  have hu := congrArg H.map (unit_single adj M)
  simp only [Functor.map_comp] at hu
  have hR := R.rightDerivedPlusSingleUnitHomology_comp_comparison (L.obj M)
  dsimp only [Functor.rightDerivedPlusSingleUnitHomology] at hR
  have hR' : H.map (R.rightDerivedPlusSingleUnit (L.obj M)) ≫ d.hom.app (L.obj M) =
      c.hom.app (R.obj (L.obj M)) ≫ R.toRightDerivedZero.app (L.obj M) := by
    rw [← hR]
    simp only [c, H, d, Category.assoc, Iso.hom_inv_id_app_assoc]
  apply (cancel_mono (R.toRightDerivedZero.app (L.obj M))).1
  dsimp only [e, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc]
  erw [hu]
  rw [Category.assoc]
  erw [hR']
  simpa only [H, c, Functor.comp_map, Functor.id_map, Functor.id_obj,
    Functor.comp_obj, Category.assoc] using
    c.hom.naturality_assoc (adj.unit.app M) (R.toRightDerivedZero.app (L.obj M))

end CategoryTheory.Adjunction
