import Langlands.Geometry.EtaleDerivedGlobalNormalization
import Langlands.Cohomology.DerivedPlusZero

/-! # Degree-zero normalization of geometric global pullback -/

noncomputable section

universe u wX wZ wR

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections
open Langlands.Cohomology.DerivedPlus Langlands.Cohomology.DerivedPlusSource

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]

/-- Actual inverse image commutes with the bounded-below singleton complex. -/
def inverseImageSingleComplexIso (F : ModuleSheaf X R) :
    (inverseImage f R).mapCochainComplexPlus.obj (singlePlus F) ≅
      singlePlus ((inverseImage f R).obj F) :=
  (CochainComplex.Plus.fullyFaithfulι _).preimageIso
    (((inverseImage f R).mapCochainComplexSingleFunctor 0).app F)

/-- Ordinary section pullback on singleton complexes, with the actual
inverse-image singleton comparison. -/
def singletonSectionsPullback (F : ModuleSheaf X R) :
    (sections X R).mapCochainComplexPlus.obj (singlePlus F) ⟶
      (sections Z R).mapCochainComplexPlus.obj
        (singlePlus ((inverseImage f R).obj F)) :=
  (sectionsComplexPullback f R).app (singlePlus F) ≫
    (sections Z R).mapCochainComplexPlus.map (inverseImageSingleComplexIso f R F).hom

private theorem inverseImageSingleComplexIso_hom (F : ModuleSheaf X R) :
    (inverseImageSingleComplexIso f R F).hom.hom =
      ((inverseImage f R).mapCochainComplexSingleFunctor 0).hom.app F := by
  change (CochainComplex.Plus.ι _).map (inverseImageSingleComplexIso f R F).hom = _
  simp only [inverseImageSingleComplexIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.app_hom]

/-- The singleton section map has the ordinary section map in degree zero. -/
theorem singletonSectionsPullback_f_zero (F : ModuleSheaf X R) :
    (singletonSectionsPullback f R F).hom.f 0 =
      (sections X R).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).hom ≫
        (sectionsPullback f R).app F ≫
          (sections Z R).map
            (HomologicalComplex.singleObjXSelf (.up ℤ) 0
              ((inverseImage f R).obj F)).inv := by
  have h := (sectionsPullback f R).naturality
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).hom
  dsimp only [Functor.comp_map] at h
  change ((sectionsComplexPullback f R).app (singlePlus F)).hom.f 0 ≫
    (sections Z R).map ((inverseImageSingleComplexIso f R F).hom.hom.f 0) = _
  rw [sectionsComplexPullback_app_f, inverseImageSingleComplexIso_hom]
  simp only [Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Functor.map_comp, ← Category.assoc]
  exact congrArg (· ≫ (sections Z R).map
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((inverseImage f R).obj F)).inv) h.symm

private theorem singletonMap_homology
    {F : ModuleSheaf X R} {G : ModuleSheaf Z R}
    (φ : (sections X R).mapCochainComplexPlus.obj (singlePlus F) ⟶
      (sections Z R).mapCochainComplexPlus.obj (singlePlus G))
    (a : (sections X R).obj F ⟶ (sections Z R).obj G)
    (hφ : φ.hom.f 0 =
      (sections X R).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).hom ≫ a ≫
        (sections Z R).map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).inv) :
    HomologicalComplex.homologyMap φ.hom 0 ≫
      (singleImageHomologyIso (sections Z R) G).hom =
        (singleImageHomologyIso (sections X R) F).hom ≫ a := by
  have hc : (singleImageCyclesIso (sections X R) F).inv ≫
      HomologicalComplex.cyclesMap φ.hom 0 =
        a ≫ (singleImageCyclesIso (sections Z R) G).inv := by
    apply (cancel_mono
      (((sections Z R).mapCochainComplexPlus.obj (singlePlus G)).obj.iCycles 0)).mp
    rw [Category.assoc, HomologicalComplex.cyclesMap_i,
      singleImageCyclesIso_inv_iCycles_assoc]
    erw [Category.assoc, singleImageCyclesIso_inv_iCycles]
    rw [hφ]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  apply (cancel_epi (singleImageHomologyIso (sections X R) F).inv).mp
  rw [← singleImageCyclesIso_inv_homologyπ, Category.assoc,
    HomologicalComplex.homologyπ_naturality_assoc, reassoc_of% hc,
    singleImageCyclesIso_inv_homologyπ_assoc, Iso.inv_hom_id, Category.comp_id,
    singleImageCyclesIso_inv_homologyπ, Iso.inv_hom_id_assoc]

variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

omit [HasDerivedCategory (ModuleCat.{u} R)] in
/-- The derived inverse-image singleton comparison uses the same localized
complex singleton comparison. -/
theorem plusSingleIso_hom_eq (F : ModuleSheaf X R) :
    (EtaleDerivedInverseImage.plusSingleIso f R 0).hom.app F =
      (EtaleDerivedInverseImage.plusFactors f R).hom.app (singlePlus F) ≫
        DerivedCategory.Plus.Q.map (inverseImageSingleComplexIso f R F).hom := by
  apply (DerivedCategory.Plus.ι (C := ModuleSheaf Z R)).map_injective
  simp only [EtaleDerivedInverseImage.plusSingleIso, EtaleDerivedInverseImage.plusFactors,
    NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Functor.map_preimage,
    Functor.map_comp]
  change ((inverseImage f R).mapDerivedCategorySingleFunctor 0).hom.app F =
    (inverseImage f R).mapDerivedCategoryFactors.hom.app
      ((CochainComplex.singleFunctor _ 0).obj F) ≫
        DerivedCategory.Q.map (inverseImageSingleComplexIso f R F).hom.hom
  rw [inverseImageSingleComplexIso_hom]
  apply (cancel_epi ((inverseImage f R).mapDerivedCategoryFactors.inv.app
    ((CochainComplex.singleFunctor _ 0).obj F))).mp
  rw [Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app,
    Iso.inv_hom_id_app_assoc]

/-- The sheaf pullback is normalized on the actual singleton unit. -/
@[reassoc] theorem sheafDerivedPullback_unit (F : ModuleSheaf X R) :
    (sections X R).rightDerivedFunctorPlusUnit.app (singlePlus F) ≫
      (sheafDerivedPullback f R).app F =
        DerivedCategory.Plus.Q.map (singletonSectionsPullback f R F) ≫
          (sections Z R).rightDerivedFunctorPlusUnit.app
            (singlePlus ((inverseImage f R).obj F)) := by
  have h := (sections Z R).rightDerivedFunctorPlusUnit.naturality
    (inverseImageSingleComplexIso f R F).hom
  dsimp only [Functor.comp_map] at h
  simp only [sheafDerivedPullback, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp]
  rw [plusSingleIso_hom_eq, Functor.map_comp]
  erw [derivedPullback_normalization_assoc]
  erw [← h, ← Functor.map_comp_assoc]
  rfl

omit [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z R)] in
private theorem singletonSectionsPullback_localized_homology (F : ModuleSheaf X R) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        (DerivedCategory.Plus.Q.map (singletonSectionsPullback f R F)) ≫
      (localizedSingleImageHomologyIso (sections Z R) ((inverseImage f R).obj F)).hom =
        (localizedSingleImageHomologyIso (sections X R) F).hom ≫
          (sectionsPullback f R).app F := by
  simp only [localizedSingleImageHomologyIso, Iso.trans_hom, Category.assoc]
  erw [localizedHomologyIso_hom_naturality_assoc]
  rw [singletonMap_homology R _ _ (singletonSectionsPullback_f_zero f R F)]

omit [HasDerivedCategory.{wZ} (ModuleSheaf Z R)] in
/-- The actual singleton derived-section unit induces the canonical
ordinary-section identification in degree zero. -/
@[reassoc] theorem sectionUnit_homology_zero (F : ModuleSheaf X R) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        ((sections X R).rightDerivedFunctorPlusUnit.app (singlePlus F)) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso X R).hom.app F =
        (localizedSingleImageHomologyIso (sections X R) F).hom := by
  change _ ≫ ((homologyNatIso (sections X R) 0).hom.app F ≫
    (sections X R).rightDerivedZeroIsoSelf.hom.app F) = _
  rw [← Category.assoc, rightDerivedFunctorPlusUnit_homology_zero,
    Category.assoc, Functor.rightDerivedZeroIsoSelf_inv_hom_id_app, Category.comp_id]

/-- Zeroth homology of the constructed derived geometric pullback is exactly
ordinary global-section pullback. -/
@[reassoc] theorem sheafDerivedPullback_zero (F : ModuleSheaf X R) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        ((sheafDerivedPullback f R).app F) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso Z R).hom.app
        ((inverseImage f R).obj F) =
      (EtaleDerivedSectionsPlus.homologyZeroIso X R).hom.app F ≫
        (sectionsPullback f R).app F := by
  have hu : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
      ((sections X R).rightDerivedFunctorPlusUnit.app (singlePlus F)) =
        (localizedSingleImageHomologyIso (sections X R) F).hom ≫
          (EtaleDerivedSectionsPlus.homologyZeroIso X R).inv.app F := by
    apply (cancel_mono ((EtaleDerivedSectionsPlus.homologyZeroIso X R).hom.app F)).mp
    rw [sectionUnit_homology_zero, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have : IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
      ((sections X R).rightDerivedFunctorPlusUnit.app (singlePlus F))) := by
    rw [hu]
    infer_instance
  apply (cancel_epi ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
    ((sections X R).rightDerivedFunctorPlusUnit.app (singlePlus F)))).mp
  rw [← Functor.map_comp_assoc, sheafDerivedPullback_unit, Functor.map_comp_assoc,
    sectionUnit_homology_zero, singletonSectionsPullback_localized_homology,
    sectionUnit_homology_zero_assoc]

/-- Through the existing cohomology-zero isomorphisms, arbitrary-morphism
cohomology pullback recovers ordinary global-section pullback. -/
@[reassoc] theorem cohomologyPullback_zero (F : ModuleSheaf X R) :
    (cohomologyPullback f R 0).app F ≫
      (cohomologyZeroIso Z R).hom.app ((inverseImage f R).obj F) =
        (cohomologyZeroIso X R).hom.app F ≫ (sectionsPullback f R).app F := by
  simp only [cohomologyPullback, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.id_comp, Category.assoc]
  change (EtaleDerivedSectionsPlus.homologyNatIso X R 0).inv.app F ≫
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
      ((sheafDerivedPullback f R).app F) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso Z R).hom.app
        ((inverseImage f R).obj F)) = _
  rw [sheafDerivedPullback_zero]
  change (EtaleDerivedSectionsPlus.homologyNatIso X R 0).inv.app F ≫
    (((EtaleDerivedSectionsPlus.homologyNatIso X R 0).hom.app F ≫
      (cohomologyZeroIso X R).hom.app F) ≫ (sectionsPullback f R).app F) = _
  rw [Category.assoc, Iso.inv_hom_id_app_assoc]

end Langlands.Geometry.EtaleDerivedGlobalPullback
