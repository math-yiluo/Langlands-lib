/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CanonicalResolutionDerivedIso
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import all Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # Resolution comparisons and the composite derived unit

Source: Stacks Project, derived.tex, Tags 015M and 015N.
(blueprint: lem-pc-grothendieck-resolution-unit-comparison).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Homology of the canonical comparison computes the prescribed resolution comparison.
Source: Stacks Project, Tag 015M, resolution computation of derived functors.
(blueprint: lem-pc-canonical-resolution-homology-comparison).

Proof: For the chosen injective resolution, expand the single-object homology comparison;
its final inverse resolution comparison cancels the resolution comparison in the left
side. For the prescribed resolution, choose a comparison lifting the identity of X.
Its extension induces a homotopy equivalence, and naturality of the derived unit shows
that the chosen derived comparison followed by its image is resolutionDerivedIso F I.
Naturality of homologyFunctorObjQIso and isoRightDerivedObjCochainComplex identifies
its map on homology with the prescribed resolution comparison. Finally expand
isoRightDerivedObjCochainComplex: its inverse map/extension homology comparison cancels
the map/extension factor in canonicalResolutionDerivedIso, and its inverse extension
homology comparison cancels the last factor on the right. This works also for n = 0.
-/
theorem resolution_homology_transport
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [EnoughInjectives A] {B : Type uB} [Category.{vB} B]
    [Abelian B] [HasDerivedCategory A]
    [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]
    (X : A) (I : InjectiveResolution X) (n : ℕ) :
    (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom ≫
          (I.isoRightDerivedObj F n).hom =
        (DerivedCategory.Plus.homologyFunctor B n).map (canonicalResolutionDerivedIso F I).hom ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso
            ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
              ComplexShape.embeddingUpNat, 0, inferInstance⟩ n).hom ≫
          (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom := by
  have hcore :
      (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom ≫
            (I.isoRightDerivedObj F n).hom =
          (DerivedCategory.Plus.homologyFunctor B n).map
            (resolutionDerivedIso F I).hom ≫
            (DerivedCategory.Plus.homologyFunctorObjQIso
              ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
                inferInstance⟩ n).hom ≫
            HomologicalComplex.homologyMap
              ((I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom) (n : ℤ) ≫
            (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
              ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom := by
    let R := injectiveResolution X
    let φ : R.Hom I (𝟙 X) :=
      ⟨InjectiveResolution.desc (𝟙 X) I R,
        by simp [InjectiveResolution.desc_commutes_zero]⟩
    have hη (L : CochainComplex.Plus A) [∀ n, Injective (L.obj.X n)] :
        IsIso (F.rightDerivedFunctorPlusUnit.app L) := by
      obtain ⟨L, n, hn⟩ := L
      let L' : CochainComplex (InjectiveObject A) ℤ :=
        HomologicalComplex.liftObjectProperty _ L inferInstance
      have hL' : L'.IsStrictlyGE n := by
        rwa [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι _)]
      exact inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnit.app
        ((InjectiveObject.ι A).mapCochainComplexPlus.obj ⟨L', n, hL'⟩)))
    let LX : CochainComplex.Plus A := ⟨R.cochainComplex, 0, inferInstance⟩
    let LY : CochainComplex.Plus A := ⟨I.cochainComplex, 0, inferInstance⟩
    have : ∀ n, Injective (LX.obj.X n) := fun n ↦
      inferInstanceAs (Injective (R.cochainComplex.X n))
    have : ∀ n, Injective (LY.obj.X n) := fun n ↦
      inferInstanceAs (Injective (I.cochainComplex.X n))
    have : IsIso (F.rightDerivedFunctorPlusUnit.app LX) := hη LX
    have : IsIso (F.rightDerivedFunctorPlusUnit.app LY) := hη LY
    let g : LX ⟶ LY := ObjectProperty.homMk φ.hom'
    have h₁ := F.rightDerivedFunctorPlusUnit.naturality g
    have h₂ : (resolutionAugmentationIso R).hom ≫ DerivedCategory.Plus.Q.map g =
        (resolutionAugmentationIso I).hom := by
      apply DerivedCategory.Plus.ι.map_injective
      simp only [resolutionAugmentationIso, Functor.map_comp, Functor.preimageIso_hom,
        Functor.map_preimage]
      dsimp
      change ((DerivedCategory.singleFunctorIsoCompQ A 0).hom.app X ≫
          DerivedCategory.Q.map R.ι') ≫ DerivedCategory.Q.map φ.hom' = _
      simp only [Category.assoc, ← Functor.map_comp, InjectiveResolution.Hom.ι'_comp_hom',
        Functor.map_id, Category.id_comp]
    let FG : F.rightDerivedPlusComplex X ⟶
        ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
          inferInstance⟩ := ObjectProperty.homMk ((F.mapHomologicalComplex _).map φ.hom')
    have hcompare : (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ X).hom ≫
        DerivedCategory.Plus.Q.map FG = (resolutionDerivedIso F I).hom := by
      have hi : inv (F.rightDerivedFunctorPlusUnit.app LX) ≫ DerivedCategory.Plus.Q.map FG =
          F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map g) ≫
            inv (F.rightDerivedFunctorPlusUnit.app LY) := by
        rw [IsIso.inv_comp_eq, ← Category.assoc]
        symm
        rw [IsIso.comp_inv_eq]
        exact h₁.symm
      have hI : (resolutionDerivedIso F I).hom =
          F.rightDerivedFunctorPlus.map (resolutionAugmentationIso I).hom ≫
            inv (F.rightDerivedFunctorPlusUnit.app LY) := by
        simp only [resolutionDerivedIso, Functor.comp_obj, Functor.mapIso_symm, Iso.trans_hom,
          Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, asIso_inv, Iso.app_hom,
          Functor.rightDerivedFunctorPlusUnit, Functor.quotientCompMapHomotopyCategoryPlusIso,
          Iso.refl_inv, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
          Functor.whiskerRight_app, NatTrans.id_app, Functor.associator_hom_app, Category.id_comp,
          IsIso.eq_comp_inv, Category.assoc, Iso.hom_inv_id_app_assoc, LY]
        erw [Functor.map_id]
        simp [← Functor.map_comp]
      rw [hI]
      change (F.rightDerivedFunctorPlus.map (resolutionAugmentationIso R).hom ≫
          inv (F.rightDerivedFunctorPlusUnit.app LX)) ≫ DerivedCategory.Plus.Q.map FG = _
      rw [Category.assoc, hi, ← Category.assoc, ← Functor.map_comp, h₂]
    have hnat := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality FG (n : ℤ)
    have hres := R.isoRightDerivedObjCochainComplex_inv_naturality φ F n
    have hhom : (F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom ≫
        (I.isoRightDerivedObjCochainComplex F n).hom =
        (DerivedCategory.Plus.homologyFunctor B n).map (resolutionDerivedIso F I).hom ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso
            ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
              inferInstance⟩ n).hom := by
      rw [← hcompare, Functor.map_comp, Category.assoc, hnat]
      simp only [Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso,
        Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
      dsimp [R] at hres
      simp only [Functor.map_id, Category.comp_id] at hres
      rw [← hres, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl
    rw [← reassoc_of% hhom]
    simp only [InjectiveResolution.isoRightDerivedObjCochainComplex, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
      Category.assoc]
    simp only [← HomologicalComplex.homologyMap_comp_assoc, Iso.inv_hom_id,
      HomologicalComplex.homologyMap_id, Category.id_comp,
      Category.comp_id]
  rw [hcore]
  simp only [canonicalResolutionDerivedIso, Iso.trans_hom, Functor.mapIso_hom]
  have hnat := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
    (K := ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
      inferInstance⟩)
    (L := ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
      ComplexShape.embeddingUpNat, 0, inferInstance⟩)
    ((CochainComplex.plus B).isoMk
      (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F)).hom n
  have hnat2 :
      (DerivedCategory.Plus.homologyFunctorObjQIso
          ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
            inferInstance⟩ n).hom ≫
        HomologicalComplex.homologyMap
          (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom (n : ℤ) =
      (DerivedCategory.Plus.homologyFunctor B n).map
          (DerivedCategory.Plus.Q.map
            ((CochainComplex.plus B).isoMk
              (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F)).hom) ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso
          ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
            ComplexShape.embeddingUpNat, 0, inferInstance⟩ n).hom := by
    simpa using hnat.symm
  calc
    _ = (DerivedCategory.Plus.homologyFunctor B n).map (resolutionDerivedIso F I).hom ≫
        ((DerivedCategory.Plus.homologyFunctorObjQIso
          ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex, 0,
            inferInstance⟩ n).hom ≫
          HomologicalComplex.homologyMap
            (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F).hom (n : ℤ)) ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom := by simp [Category.assoc]
    _ = (DerivedCategory.Plus.homologyFunctor B n).map (resolutionDerivedIso F I).hom ≫
        ((DerivedCategory.Plus.homologyFunctor B n).map
          (DerivedCategory.Plus.Q.map
            ((CochainComplex.plus B).isoMk
              (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat F)).hom) ≫
          (DerivedCategory.Plus.homologyFunctorObjQIso
            ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
              ComplexShape.embeddingUpNat, 0, inferInstance⟩ n).hom) ≫
        (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom := by rw [hnat2]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

end CategoryTheory
