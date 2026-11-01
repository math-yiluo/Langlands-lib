import Langlands.Cohomology.DerivedPlusSource
import Langlands.Cohomology.DerivedExactComposition
import Mathlib.Algebra.Homology.SingleHomology

/-! # Zeroth homology of the actual right-derived unit -/

noncomputable section

namespace Langlands.Cohomology.DerivedPlus

open CategoryTheory CategoryTheory.Limits
open DerivedPlusSource

universe w w' v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- An object as an actual bounded-below singleton complex. -/
def singlePlus (X : C) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C 0).obj X, ⟨0, inferInstance⟩⟩

/-- Cycles of an additive functor applied to a singleton recover its value. -/
def singleImageCyclesIso (X : C) :
    (F.mapCochainComplexPlus.obj (singlePlus X)).obj.cycles 0 ≅ F.obj X :=
  ((F.mapCochainComplexPlus.obj (singlePlus X)).obj.iCyclesIso 0 1 (by simp)
    (by simp [singlePlus, CochainComplex.singleFunctor])) ≪≫
    F.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X)

/-- Homology of the same singleton recovers the ordinary functor value. -/
def singleImageHomologyIso (X : C) :
    (F.mapCochainComplexPlus.obj (singlePlus X)).obj.homology 0 ≅ F.obj X :=
  ((F.mapCochainComplexPlus.obj (singlePlus X)).obj.isoHomologyπ (-1) 0 (by simp)
    (by simp [singlePlus, CochainComplex.singleFunctor])).symm ≪≫ singleImageCyclesIso F X

/-- Localized singleton homology with its actual ordinary value. -/
def localizedSingleImageHomologyIso (X : C) :
    (DerivedCategory.Plus.homologyFunctor D 0).obj
      (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj (singlePlus X))) ≅
        F.obj X :=
  localizedHomologyIso _ 0 ≪≫ singleImageHomologyIso F X

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] in
@[reassoc] theorem singleImageCyclesIso_inv_iCycles (X : C) :
    (singleImageCyclesIso F X).inv ≫
      (F.mapCochainComplexPlus.obj (singlePlus X)).obj.iCycles 0 =
        F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv := by
  simp [singleImageCyclesIso]

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] in
@[reassoc] theorem singleImageCyclesIso_inv_homologyπ (X : C) :
    (singleImageCyclesIso F X).inv ≫
      (F.mapCochainComplexPlus.obj (singlePlus X)).obj.homologyπ 0 =
        (singleImageHomologyIso F X).inv := by
  simp [singleImageHomologyIso]

omit [EnoughInjectives C] in
/-- The singleton-to-resolution comparison is localization of the actual augmentation. -/
theorem singleIsoOfResolution_hom_eq_localized_augmentation {X : C} (I : InjectiveResolution X) :
    (singleIsoOfResolution I).hom =
      DerivedCategory.Plus.Q.map (ObjectProperty.homMk I.ι' : singlePlus X ⟶ resolutionPlus I) := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [ι_map_singleIsoOfResolution_hom]
  simp only [DerivedCategory.Plus.singleFunctorιIso, DerivedCategory.singleFunctorIsoCompQ,
    Iso.refl_hom, DerivedCategory.Plus.QCompιIso_inv_app]
  change 𝟙 _ ≫ 𝟙 _ ≫ DerivedCategory.Q.map I.ι' ≫ 𝟙 _ = DerivedCategory.Q.map I.ι'
  simp only [Category.id_comp, Category.comp_id]

/-- Naturality of the right-derived unit at the actual resolution augmentation. -/
@[reassoc] theorem singleUnit_comp_derivedComplexIso {X : C} (I : InjectiveResolution X) :
    F.rightDerivedFunctorPlusUnit.app (singlePlus X) ≫ (derivedComplexIso F I).hom =
      DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map
        (ObjectProperty.homMk I.ι' : singlePlus X ⟶ resolutionPlus I)) := by
  change F.rightDerivedFunctorPlusUnit.app (singlePlus X) ≫
    (F.rightDerivedFunctorPlus.map (singleIsoOfResolution I).hom ≫
      inv (F.rightDerivedFunctorPlusUnit.app (resolutionPlus I))) = _
  rw [singleIsoOfResolution_hom_eq_localized_augmentation]
  have h := F.rightDerivedFunctorPlusUnit.naturality
    (ObjectProperty.homMk I.ι' : singlePlus X ⟶ resolutionPlus I)
  dsimp only [Functor.comp_map] at h
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The actual augmentation after applying the additive functor and extending
the natural-indexed image resolution by zero. -/
def singleToImageResolution {X : C} (I : InjectiveResolution X) :
    F.mapCochainComplexPlus.obj (singlePlus X) ⟶ imageResolution F I :=
  F.mapCochainComplexPlus.map
    (ObjectProperty.homMk I.ι' : singlePlus X ⟶ resolutionPlus I) ≫
      (imageResolutionComparison F I).hom

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] in
/-- The cycles of the augmented image complex recover the ordinary
resolution map into degree-zero cycles. -/
@[reassoc] theorem singleToImageResolution_cycles {X : C} (I : InjectiveResolution X) :
    (singleImageCyclesIso F X).inv ≫
      HomologicalComplex.cyclesMap (singleToImageResolution F I).hom 0 ≫
      (((F.mapHomologicalComplex _).obj I.cocomplex).extendCyclesIso
        ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).hom =
      I.toRightDerivedZero' F := by
  have hc : (imageResolutionComparison F I).hom.hom =
      (mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).inv := by
    change (CochainComplex.Plus.ι D).map (imageResolutionComparison F I).hom = _
    simp only [imageResolutionComparison, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage, Iso.symm_hom]
  apply (cancel_mono (((F.mapHomologicalComplex _).obj I.cocomplex).iCycles 0)).mp
  rw [Category.assoc, Category.assoc,
    HomologicalComplex.extendCyclesIso_hom_iCycles]
  erw [HomologicalComplex.cyclesMap_i_assoc,
    singleImageCyclesIso_inv_iCycles_assoc,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  simp only [singleToImageResolution, ObjectProperty.FullSubcategory.comp_hom, hc,
    HomologicalComplex.comp_f, Category.assoc]
  change F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫
    F.map (I.ι'.f 0) ≫
    (mapExtendIso F I.cocomplex ComplexShape.embeddingUpNat).inv.f 0 ≫
    (((F.mapHomologicalComplex _).obj I.cocomplex).extendXIso
      ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).hom = _
  rw [← map_extendXIso_hom, I.ι'_f_zero]
  simp only [InjectiveResolution.cochainComplexXIso, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

omit [HasDerivedCategory C] [EnoughInjectives C] [HasDerivedCategory D] in
/-- Zeroth homology of the augmented image complex is the canonical ordinary
resolution-to-derived-functor map before the resolution comparison. -/
theorem singleToImageResolution_homology {X : C} (I : InjectiveResolution X) :
    (singleImageHomologyIso F X).inv ≫
      HomologicalComplex.homologyMap (singleToImageResolution F I).hom 0 ≫
      (((F.mapHomologicalComplex _).obj I.cocomplex).extendHomologyIso
        ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).hom =
      I.toRightDerivedZero' F ≫
        ((F.mapHomologicalComplex _).obj I.cocomplex).homologyπ 0 := by
  rw [← singleImageCyclesIso_inv_homologyπ, Category.assoc,
    HomologicalComplex.homologyπ_naturality_assoc]
  erw [HomologicalComplex.homologyπ_extendHomologyIso_hom,
    singleToImageResolution_cycles_assoc]

/-- On zeroth homology, the actual bounded-below right-derived unit is
the canonical map from the ordinary functor to its zeroth right-derived functor. -/
theorem rightDerivedFunctorPlusUnit_homology_zero (X : C) :
    (DerivedCategory.Plus.homologyFunctor D 0).map
        (F.rightDerivedFunctorPlusUnit.app (singlePlus X)) ≫
      (homologyNatIso F 0).hom.app X =
        (localizedSingleImageHomologyIso F X).hom ≫ F.toRightDerivedZero.app X := by
  let I := injectiveResolution X
  have hu : F.rightDerivedFunctorPlusUnit.app (singlePlus X) ≫
      (imageResolutionIso F I).hom =
        DerivedCategory.Plus.Q.map (singleToImageResolution F I) := by
    simp only [imageResolutionIso, Iso.trans_hom, Functor.mapIso_hom,
      ← Category.assoc, singleUnit_comp_derivedComplexIso, ← Functor.map_comp,
      singleToImageResolution]
  have hz :
      HomologicalComplex.homologyMap (singleToImageResolution F I).hom 0 ≫
        (((F.mapHomologicalComplex _).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat (j := 0) (j' := 0) rfl).hom =
        (singleImageHomologyIso F X).hom ≫ I.toRightDerivedZero' F ≫
          ((F.mapHomologicalComplex _).obj I.cocomplex).homologyπ 0 := by
    apply (cancel_epi (singleImageHomologyIso F X).inv).mp
    rw [singleToImageResolution_homology, Iso.inv_hom_id_assoc]
  rw [homologyNatIso_hom_app F 0 I, ← imageHomologyIso_comp F I 0]
  erw [← Functor.map_comp_assoc, hu]
  simp only [imageHomologyIso, Iso.trans_hom, Category.assoc]
  erw [localizedHomologyIso_hom_naturality_assoc]
  erw [reassoc_of% hz, I.toRightDerivedZero_eq F]
  simp only [localizedSingleImageHomologyIso, Iso.trans_hom, Category.assoc]
  rfl

end Langlands.Cohomology.DerivedPlus
