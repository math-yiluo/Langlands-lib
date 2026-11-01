import Langlands.Cohomology.DerivedPlusSourceLocalization
import Langlands.Geometry.EtaleDerivedGlobalZero
import Langlands.Geometry.EtaleRestrictionSectionComparison

/-! # Actual resolution comparison for geometric etale pullback -/

noncomputable section

universe u wX wZ wR

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections
open Langlands.Cohomology Langlands.Cohomology.DerivedPlus
open Langlands.Cohomology.DerivedPlusSource

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]
  (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]

private theorem imageResolutionComparison_hom
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (G : C ⥤ D) [G.Additive] {F : C} (I : InjectiveResolution F) :
    (imageResolutionComparison G I).hom.hom =
      (mapExtendIso G I.cocomplex ComplexShape.embeddingUpNat).inv := by
  change (CochainComplex.Plus.ι D).map (imageResolutionComparison G I).hom = _
  simp only [imageResolutionComparison, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.symm_hom]

omit [HasDerivedCategory (ModuleSheaf X R)] [HasDerivedCategory (ModuleSheaf Z R)] in
/-- The actual geometric section map on a resolution is the extension of its
ordinary degreewise square, through the constructed extension comparisons. -/
@[reassoc] theorem sectionsComplexPullback_resolution {F : ModuleSheaf X R}
    (I : InjectiveResolution F) :
    (sectionsComplexPullback f R).app (resolutionPlus I) ≫
      (sections Z R).mapCochainComplexPlus.map
        (mappedResolutionComplexIso (inverseImage f R) I).hom ≫
      (imageResolutionComparison (sections Z R)
        (DerivedComparison.mapInjectiveResolution (inverseImage f R) I)).hom =
    (imageResolutionComparison (sections X R) I).hom ≫
      imageResolutionSquare (sections X R) (inverseImage f R) (sections Z R)
        (sectionsPullback f R) I := by
  have hs :
      ((sectionsComplexPullback f R).app (resolutionPlus I)).hom =
        (NatTrans.mapHomologicalComplex (sectionsPullback f R) (.up ℤ)).app
          I.cochainComplex := by
    apply HomologicalComplex.hom_ext
    intro i
    exact sectionsComplexPullback_app_f f R (resolutionPlus I) i
  apply (CochainComplex.Plus.ι (ModuleCat.{u} R)).map_injective
  change ((sectionsComplexPullback f R).app (resolutionPlus I)).hom ≫
      ((sections Z R).mapHomologicalComplex (.up ℤ)).map
        (mappedResolutionComplexIso (inverseImage f R) I).hom.hom ≫
      (imageResolutionComparison (sections Z R)
        (DerivedComparison.mapInjectiveResolution (inverseImage f R) I)).hom.hom =
    (imageResolutionComparison (sections X R) I).hom.hom ≫ _
  rw [hs, mappedResolutionComplexIso_hom, imageResolutionComparison_hom,
    imageResolutionComparison_hom]
  change (NatTrans.mapHomologicalComplex (sectionsPullback f R) (.up ℤ)).app
      I.cochainComplex ≫
      ((sections Z R).mapHomologicalComplex (.up ℤ)).map
        (mapExtendIso (inverseImage f R) I.cocomplex ComplexShape.embeddingUpNat).inv ≫
      (mapExtendIso (sections Z R)
        (((inverseImage f R).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
        ComplexShape.embeddingUpNat).inv =
    (mapExtendIso (sections X R) I.cocomplex ComplexShape.embeddingUpNat).inv ≫
      HomologicalComplex.extendMap
        ((NatTrans.mapHomologicalComplex (sectionsPullback f R) (.up ℕ)).app
          I.cocomplex) ComplexShape.embeddingUpNat
  rw [← mapExtendIso_comp_inv]
  exact extendMapIso_hom_app ComplexShape.embeddingUpNat (sectionsPullback f R) I.cocomplex

/-- Exact geometric inverse image carries the actual localized resolution
augmentation to the augmentation of its mapped injective resolution. -/
@[reassoc] theorem plusSingleIso_resolution {F : ModuleSheaf X R}
    (I : InjectiveResolution F) :
    (EtaleDerivedInverseImage.plusFunctor f R).map (singleIsoOfResolution I).hom ≫
      (EtaleDerivedInverseImage.plusFactors f R).hom.app (resolutionPlus I) ≫
        DerivedCategory.Plus.Q.map (mappedResolutionComplexIso (inverseImage f R) I).hom =
      (EtaleDerivedInverseImage.plusSingleIso f R 0).hom.app F ≫
        (singleIsoOfResolution
          (DerivedComparison.mapInjectiveResolution (inverseImage f R) I)).hom := by
  apply (DerivedCategory.Plus.ι (C := ModuleSheaf Z R)).map_injective
  simp only [Functor.map_comp, EtaleDerivedInverseImage.plusSingleIso,
    EtaleDerivedInverseImage.plusFactors, NatIso.ofComponents_hom_app,
    Functor.preimageIso_hom, Functor.map_preimage,
    singleIsoOfResolution_hom_eq_localized_augmentation]
  change (inverseImage f R).mapDerivedCategory.map (DerivedCategory.Q.map I.ι') ≫
      (inverseImage f R).mapDerivedCategoryFactors.hom.app I.cochainComplex ≫
        DerivedCategory.Q.map (mappedResolutionComplexIso (inverseImage f R) I).hom.hom =
    ((inverseImage f R).mapDerivedCategorySingleFunctor 0).hom.app F ≫
      DerivedCategory.Q.map
        (DerivedComparison.mapInjectiveResolution (inverseImage f R) I).ι'
  apply (cancel_epi
    (((inverseImage f R).mapDerivedCategorySingleFunctor 0).inv.app F)).mp
  simpa only [localizedMappedResolutionIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
    mappedResolutionComplexIso_hom] using
    localizedMappedResolutionIso_augmentation (inverseImage f R) I

variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Every actual injective resolution computes geometric sheaf-derived
pullback by the ordinary section square on its mapped resolution. -/
@[reassoc] theorem sheafDerivedPullback_resolution {F : ModuleSheaf X R}
    (I : InjectiveResolution F) :
    (sheafDerivedPullback f R).app F ≫
      (imageResolutionIso (sections Z R)
        (DerivedComparison.mapInjectiveResolution (inverseImage f R) I)).hom =
    (imageResolutionIso (sections X R) I).hom ≫
      DerivedCategory.Plus.Q.map
        (imageResolutionSquare (sections X R) (inverseImage f R) (sections Z R)
          (sectionsPullback f R) I) := by
  have hn := (derivedPullback f R).naturality (singleIsoOfResolution I).hom
  dsimp only [Functor.comp_map, EtaleDerivedSectionsPlus.rightDerivedFunctor] at hn
  have hu := (sections Z R).rightDerivedFunctorPlusUnit.naturality
    (mappedResolutionComplexIso (inverseImage f R) I).hom
  dsimp only [Functor.comp_map] at hu
  simp only [sheafDerivedPullback, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, imageResolutionIso, derivedComplexIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  change (derivedPullback f R).app
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) 0).obj F) ≫
      (sections Z R).rightDerivedFunctorPlus.map
        ((EtaleDerivedInverseImage.plusSingleIso f R 0).hom.app F) ≫
      (sections Z R).rightDerivedFunctorPlus.map
        (singleIsoOfResolution
          (DerivedComparison.mapInjectiveResolution (inverseImage f R) I)).hom ≫
      inv ((sections Z R).rightDerivedFunctorPlusUnit.app
        (resolutionPlus (DerivedComparison.mapInjectiveResolution (inverseImage f R) I))) ≫
      DerivedCategory.Plus.Q.map
        (imageResolutionComparison (sections Z R)
          (DerivedComparison.mapInjectiveResolution (inverseImage f R) I)).hom =
    (sections X R).rightDerivedFunctorPlus.map (singleIsoOfResolution I).hom ≫ _
  rw [← Functor.map_comp_assoc, ← plusSingleIso_resolution f R I,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hn]
  refine congrArg
    ((sections X R).rightDerivedFunctorPlus.map (singleIsoOfResolution I).hom ≫ ·) ?_
  apply (cancel_epi
    ((sections X R).rightDerivedFunctorPlusUnit.app (resolutionPlus I))).mp
  erw [derivedPullback_normalization_assoc]
  rw [← reassoc_of% hu, IsIso.hom_inv_id_assoc]
  simp only [← Functor.map_comp]
  rw [sectionsComplexPullback_resolution]
  rw [Functor.map_comp]
  simp only [IsIso.hom_inv_id_assoc]

/-- An actual isomorphism of arrows identifies geometric derived pullback with
its localized ordinary section square on any injective resolution. -/
def sheafDerivedPullbackResolutionIso {F : ModuleSheaf X R}
    (I : InjectiveResolution F) :
    Arrow.mk ((sheafDerivedPullback f R).app F) ≅
      Arrow.mk (DerivedCategory.Plus.Q.map
        (imageResolutionSquare (sections X R) (inverseImage f R) (sections Z R)
          (sectionsPullback f R) I)) :=
  Arrow.isoMk (imageResolutionIso (sections X R) I)
    (imageResolutionIso (sections Z R)
      (DerivedComparison.mapInjectiveResolution (inverseImage f R) I))
    (sheafDerivedPullback_resolution f R I).symm

/-- The derived pullback from the geometric adjunction is the actual
mapped-resolution derived square for the constructed inverse image. -/
theorem sheafDerivedPullback_eq_derivedMap :
    sheafDerivedPullback f R =
      derivedMap (sections X R) (inverseImage f R) (sections Z R)
        (sectionsPullback f R) := by
  apply NatTrans.ext
  funext F
  let I := injectiveResolution F
  rw [derivedMap_app (sections X R) (inverseImage f R) (sections Z R)
    (sectionsPullback f R) I]
  apply (cancel_mono
    (imageResolutionIso (sections Z R)
      (DerivedComparison.mapInjectiveResolution (inverseImage f R) I)).hom).mp
  simp only [derivedMapOfResolution, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact sheafDerivedPullback_resolution f R I

end Langlands.Geometry.EtaleDerivedGlobalPullback
