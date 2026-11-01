import Langlands.Geometry.EtaleDerivedGlobalPullback

/-! # Geometric normalization of arbitrary derived global pullback -/

noncomputable section

universe u wX wZ wR

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]

/-- Ordinary geometric section pullback from the actual inverse/direct
adjunction unit and preserved-terminal section comparison. -/
def sectionsPullback : sections X R ⟶ inverseImage f R ⋙ sections Z R :=
  (sections X R).leftUnitor.inv ≫
    Functor.whiskerRight (inverseImageAdjunction f R).unit (sections X R) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (EtaleDerivedDirectImage.directImageSectionsIso f R).hom

/-- The same actual termwise section map on bounded-below complexes. -/
def sectionsComplexPullback :
    (sections X R).mapCochainComplexPlus ⟶
      (inverseImage f R).mapCochainComplexPlus ⋙ (sections Z R).mapCochainComplexPlus :=
  (sections X R).mapCochainComplexPlus.leftUnitor.inv ≫
    Functor.whiskerRight (EtaleDerivedAdjunction.complexPlusAdjunction f R).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (sectionsComplexIso f R).hom

private theorem complexPlus_unit_hom (K : CochainComplex.Plus (ModuleSheaf X R)) :
    ((EtaleDerivedAdjunction.complexPlusAdjunction f R).unit.app K).hom =
      (Langlands.Cohomology.complexAdjunction (inverseImageAdjunction f R) (.up ℤ)).unit.app
        K.obj := by
  change (CochainComplex.Plus.ι (ModuleSheaf X R)).map
    ((EtaleDerivedAdjunction.complexPlusAdjunction f R).unit.app K) = _
  rw [EtaleDerivedAdjunction.complexPlusAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app]
  simp [Functor.mapCochainComplexPlusCompι]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- At every integer degree the complex comparison is the same actual
ordinary geometric section pullback. -/
theorem sectionsComplexPullback_app_f
    (K : CochainComplex.Plus (ModuleSheaf X R)) (i : ℤ) :
    ((sectionsComplexPullback f R).app K).hom.f i =
      (sectionsPullback f R).app (K.obj.X i) := by
  simp [sectionsComplexPullback, sectionsPullback, sectionsComplexIso,
    Functor.mapCochainComplexPlus, complexPlus_unit_hom]
  congr 1
  change ((CochainComplex.Plus.ι (ModuleCat.{u} R)).map
    ((CochainComplex.Plus.ι (ModuleCat.{u} R)).preimage _)).f i = _
  rw [Functor.map_preimage]
  rfl

variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

private theorem composite_unit_normalized
    (K : CochainComplex.Plus (ModuleSheaf Z R)) :
    (sections X R).rightDerivedFunctorPlusUnit.app
        ((EtaleDirectImage.directImage f (ModuleCat.{u} R)).mapCochainComplexPlus.obj K) ≫
      (sections X R).rightDerivedFunctorPlus.map
        ((EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit.app K) ≫
      (directImageSectionsIso f R).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map ((sectionsComplexIso f R).hom.app K) ≫
      (sections Z R).rightDerivedFunctorPlusUnit.app K := by
  apply (cancel_epi (DerivedCategory.Plus.Q.map ((sectionsComplexIso f R).inv.app K))).mp
  have h := directImageSectionsIso_unit f R K
  dsimp only [Functor.comp_obj] at h ⊢
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [compositeUnit, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc] using h

/-- Every complex representative recovers ordinary termwise geometric section
pullback through the actual right-derived units and inverse localization iso. -/
@[reassoc] theorem derivedPullback_normalization
    (K : CochainComplex.Plus (ModuleSheaf X R)) :
    (sections X R).rightDerivedFunctorPlusUnit.app K ≫
        (derivedPullback f R).app (DerivedCategory.Plus.Q.obj K) ≫
        (EtaleDerivedSectionsPlus.rightDerivedFunctor Z R).map
          ((EtaleDerivedInverseImage.plusFactors f R).hom.app K) =
      DerivedCategory.Plus.Q.map ((sectionsComplexPullback f R).app K) ≫
        (sections Z R).rightDerivedFunctorPlusUnit.app
          ((inverseImage f R).mapCochainComplexPlus.obj K) := by
  have he := (directImageSectionsIso f R).hom.naturality
    ((EtaleDerivedInverseImage.plusFactors f R).hom.app K)
  have hu := EtaleDerivedAdjunction.unit_app_Q f R K
  have hs := (sections X R).rightDerivedFunctorPlusUnit.naturality
    ((EtaleDerivedAdjunction.complexPlusAdjunction f R).unit.app K)
  dsimp only [EtaleDerivedSectionsPlus.rightDerivedFunctor,
    EtaleDerivedDirectImage.rightDerivedFunctor,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj] at he hu hs ⊢
  rw [derivedPullback_app]
  dsimp only [EtaleDerivedSectionsPlus.rightDerivedFunctor,
    EtaleDerivedDirectImage.rightDerivedFunctor, Functor.comp_obj, Functor.id_obj]
  simp only [Category.assoc]
  rw [← he, ← Functor.map_comp_assoc, hu, Functor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hs, composite_unit_normalized]
  simp [sectionsComplexPullback, Functor.map_comp, Category.assoc]

end Langlands.Geometry.EtaleDerivedGlobalPullback
