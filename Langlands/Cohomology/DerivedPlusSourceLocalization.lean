import Langlands.Cohomology.DerivedPlusZero
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Localization of exact images of injective resolutions -/

noncomputable section

universe uC vC uD vD wC wD

namespace Langlands.Cohomology.DerivedPlusSource

open CategoryTheory CategoryTheory.Limits
open DerivedPlus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [T.PreservesInjectiveObjects]

/-- Applying the exact source functor before or after extension of its
mapped injective resolution gives the same actual bounded-below complex. -/
def mappedResolutionComplexIso {X : C} (I : InjectiveResolution X) :
    T.mapCochainComplexPlus.obj (resolutionPlus I) ≅
      resolutionPlus (DerivedComparison.mapInjectiveResolution T I) :=
  imageResolutionComparison T I

/-- The comparison is the existing extension-by-zero comparison. -/
theorem mappedResolutionComplexIso_hom {X : C} (I : InjectiveResolution X) :
    (mappedResolutionComplexIso T I).hom.hom =
      (mapExtendIso T I.cocomplex ComplexShape.embeddingUpNat).inv := by
  change (CochainComplex.Plus.ι D).map (mappedResolutionComplexIso T I).hom = _
  simp only [mappedResolutionComplexIso, imageResolutionComparison,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.symm_hom]

/-- The termwise comparison carries the actual image augmentation to the
augmentation of the mapped injective resolution. -/
theorem mappedResolutionComplexIso_augmentation {X : C} (I : InjectiveResolution X) :
    ((T.mapCochainComplexSingleFunctor 0).inv.app X) ≫
      (T.mapHomologicalComplex (.up ℤ)).map I.ι' ≫
        (mappedResolutionComplexIso T I).hom.hom =
      (DerivedComparison.mapInjectiveResolution T I).ι' := by
  apply HomologicalComplex.from_single_hom_ext
  rw [mappedResolutionComplexIso_hom]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    InjectiveResolution.ι'_f_zero]
  simp only [CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  apply (cancel_mono
    ((DerivedComparison.mapInjectiveResolution T I).cochainComplexXIso 0 0 rfl).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  dsimp only [InjectiveResolution.cochainComplexXIso]
  rw [← map_extendXIso_hom]
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]
  simp only [T.map_comp, Category.assoc, Category.id_comp]
  rw [← T.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  exact Category.id_comp _

section Localization

variable [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

/-- The exact derived functor on the localized resolution is represented by
its actual mapped injective resolution. -/
def localizedMappedResolutionIso {X : C} (I : InjectiveResolution X) :
    T.mapDerivedCategory.obj (DerivedCategory.Q.obj I.cochainComplex) ≅
      DerivedCategory.Q.obj (DerivedComparison.mapInjectiveResolution T I).cochainComplex :=
  T.mapDerivedCategoryFactors.app I.cochainComplex ≪≫
    DerivedCategory.Q.mapIso ((mapExtendIso T I.cocomplex ComplexShape.embeddingUpNat).symm)

/-- The actual singleton comparison, localization factor and mapped resolution
comparison carry the original augmentation to the mapped augmentation. -/
theorem localizedMappedResolutionIso_augmentation {X : C} (I : InjectiveResolution X) :
    (T.mapDerivedCategorySingleFunctor 0).inv.app X ≫
      T.mapDerivedCategory.map (DerivedCategory.Q.map I.ι') ≫
        (localizedMappedResolutionIso T I).hom =
      DerivedCategory.Q.map (DerivedComparison.mapInjectiveResolution T I).ι' := by
  simp only [localizedMappedResolutionIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom, ← Category.assoc]
  rw [Category.assoc _ _ (T.mapDerivedCategoryFactors.hom.app I.cochainComplex),
    T.mapDerivedCategoryFactors_hom_naturality]
  simp only [← Category.assoc]
  rw [T.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  simpa only [Category.assoc, mappedResolutionComplexIso_hom] using
    congrArg DerivedCategory.Q.map (mappedResolutionComplexIso_augmentation T I)

end Localization

end Langlands.Cohomology.DerivedPlusSource
