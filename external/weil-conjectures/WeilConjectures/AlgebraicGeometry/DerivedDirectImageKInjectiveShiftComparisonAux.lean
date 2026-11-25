/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSplitTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Naturality component for the shifted K-injective comparison

Source: Stacks Project, Tag 079V.
(blueprint: lem-pc-direct-image-kinjective-comparison-shift-aux)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 8

noncomputable section
namespace AlgebraicGeometry.RingedSpace

-- The equivalence comparison unfolds into nested whiskerings.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- Express the restricted unit using the transported comparison and equivalence unit.
private lemma unit_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] :
    NatTrans.CommShift (Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal)
      F.rightDerivedFunctorUnit) ℤ := by
  let E := HomotopyCategory.KInjectives.equivalence C
  let B := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal ⋙
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have h : Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal)
      F.rightDerivedFunctorUnit =
      (Functor.leftUnitor B).inv ≫
        Functor.whiskerRight E.unitIso.hom B ≫
        (Functor.associator E.functor E.inverse B).hom ≫
        Functor.whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (Functor.associator _ _ _).hom := by
    ext M
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.mapHomotopyCategory_obj,
      Functor.whiskerLeft_app, Functor.asEquivalence_functor,
      Functor.rightDerivedFunctorIsoKInjectives, Iso.trans_symm, Iso.symm_symm_eq,
      Functor.isoWhiskerLeft_trans, Iso.trans_inv, Functor.isoWhiskerLeft_inv, Iso.symm_inv,
      asIso_hom, Functor.whiskerLeft_twice, ← Category.assoc, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_comp, NatTrans.comp_app, Functor.id_obj, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Functor.comp_map, ObjectProperty.ι_map, Category.id_comp,
      Functor.associator_hom_app, Category.comp_id, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, B, E]
    change _ = ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
      ((ObjectProperty.ι _).map (E.unitIso.hom.app M)) ≫
        F.rightDerivedFunctorUnit.app _) ≫ _
    erw [F.rightDerivedFunctorUnit.naturality]
    simp only [Functor.comp_map, Category.assoc, ← Functor.map_comp]
    change _ = F.rightDerivedFunctorUnit.app M.obj ≫ F.rightDerivedFunctor.map
      (E.functor.map (E.unitIso.hom.app M) ≫ E.counitIso.hom.app (E.functor.obj M))
    rw [E.functor_unitIso_comp]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [h]
  infer_instance

-- Every homotopy-category object maps to a K-injective by a quasi-isomorphism.
private lemma unit_commShift_all
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  have := unit_commShift F
  apply NatTrans.CommShift.of_whiskerLeft F.rightDerivedFunctorUnit
    (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal)
  intro M
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨L, hL, i, _hi, hqi⟩ := HasKInjectiveResolutions.exists_isKInjective K
  let _ := hL
  let _ := hqi
  refine ⟨HomotopyCategory.KInjectives.mk L,
    (HomotopyCategory.quotient _ _).map i, ?_⟩
  change IsIso (F.rightDerivedFunctor.map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map i)))
  have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map i)) := by
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) i).mpr
      (inferInstanceAs (IsIso (DerivedCategory.Q.map i)))
  infer_instance

-- Associators align the shift structures on the intermediate composite functors.
private def comparison {X Y : RingedSpace.{u}} (g : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))] :
    (moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedModuleDirectImage g :=
  (Functor.isoWhiskerLeft
    ((moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ))
    (DerivedCategory.quotientCompQhIso _)).inv ≫
  (Functor.associator _ _ _).inv ≫
  (Functor.isoWhiskerRight
    ((moduleDirectImage g).mapHomotopyCategoryFactors (ComplexShape.up ℤ))
    DerivedCategory.Qh).inv ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (HomotopyCategory.quotient _ _)
    (moduleDirectImage g).rightDerivedFunctorUnit ≫
  (Functor.associator _ _ _).inv ≫
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
    (derivedModuleDirectImage g)).hom

private lemma comparison_app {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [K.IsKInjective] :
    (comparison g).app K = (derivedModuleDirectImageKInjectiveIso g K).inv := by
  simp [comparison, derivedModuleDirectImageKInjectiveIso]

-- Shift comparison expands through several composite functors and their isomorphisms.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison after applying the inverse derived shift map is the shifted
comparison followed by the inverse localized shift identification.
Source: Stacks Project, Tag 079V.
(blueprint: lem-pc-direct-image-kinjective-comparison-shift-aux)

Proof: express the unit restricted to K-injectives in terms of the comparison
used to transport the derived shift structure and the unit of the K-injective
equivalence. Naturality and the equivalence triangle identity identify this
expression with the right-derived unit, so that unit commutes with shifts.
Extend this compatibility to every homotopy-category object using its
quasi-isomorphism to a K-injective resolution. Whisker with the quotient functor
and the localization identifications to obtain the complex-level comparison.
Its component at a K-injective is the inverse of the displayed comparison iso.
Apply its shift-compatibility equation and cancel the two comparison isomorphisms
and the localized shift identification to obtain the claimed equation. -/
theorem derivedModuleDirectImageKInjectiveIso_shift_aux
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [K.IsKInjective] :
    (derivedModuleDirectImage g).map
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app K) ≫
      (derivedModuleDirectImageKInjectiveIso g (K⟦(1 : ℤ)⟧)).hom =
    ((derivedModuleDirectImage g).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj K) ≫
      (derivedModuleDirectImageKInjectiveIso g K).hom⟦(1 : ℤ)⟧' ≫
      (moduleDirectImageLocalizedShiftIso g K).inv := by
  have := unit_commShift_all (moduleDirectImage g)
  have : NatTrans.CommShift
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (moduleRings Y))).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have : NatTrans.CommShift
      ((moduleDirectImage g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have : NatTrans.CommShift (comparison g) ℤ := by
    dsimp only [comparison]
    simp only [Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerRight_hom]
    infer_instance
  have h := NatTrans.shift_app_comm (comparison g) (1 : ℤ) K
  simp only [Functor.commShiftIso_comp_hom_app, comparison_app] at h
  change (moduleDirectImageLocalizedShiftIso g K).hom ≫
      (derivedModuleDirectImageKInjectiveIso g K).inv⟦(1 : ℤ)⟧' =
    (derivedModuleDirectImageKInjectiveIso g (K⟦(1 : ℤ)⟧)).inv ≫
      (derivedModuleDirectImage g).map
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K) ≫
      ((derivedModuleDirectImage g).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj K) at h
  rw [← cancel_epi ((derivedModuleDirectImage g).map
    ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K))]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← cancel_epi (derivedModuleDirectImageKInjectiveIso g (K⟦(1 : ℤ)⟧)).inv]
  rw [Iso.inv_hom_id]
  simp only [← Category.assoc]
  simp only [← Category.assoc] at h
  rw [← h]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]

end AlgebraicGeometry.RingedSpace
