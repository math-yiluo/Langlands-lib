import Langlands.Geometry.EtaleDerivedInverseImageCoherence

/-! # Identity and composition of actual derived global pullback -/

noncomputable section

universe u wX wZ wV wR

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections EtaleDerivedInverseImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z V : Scheme.{u}} (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- The actual derived section pullback for the identity, followed by the
constructed coefficient identification, is the identity transformation. -/
theorem derivedPullback_id_eq :
    derivedPullback (𝟙 X) R ≫
        Functor.whiskerRight (plusFunctorId R X).hom
          (EtaleDerivedSectionsPlus.rightDerivedFunctor X R) ≫
        (EtaleDerivedSectionsPlus.rightDerivedFunctor X R).leftUnitor.hom = 𝟙 _ := by
  apply Functor.rightDerived_ext (sections X R).rightDerivedFunctorPlus
    (sections X R).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso (ModuleSheaf X R))
  apply NatTrans.ext
  funext K
  change (sections X R).rightDerivedFunctorPlusUnit.app K ≫
      (derivedPullback (𝟙 X) R).app (DerivedCategory.Plus.Q.obj K) ≫
      (sections X R).rightDerivedFunctorPlus.map
        ((plusFunctorId R X).hom.app (DerivedCategory.Plus.Q.obj K)) ≫ 𝟙 _ =
    (sections X R).rightDerivedFunctorPlusUnit.app K ≫ 𝟙 _
  rw [plusFunctorId_hom_app_Q, Functor.map_comp]
  simp only [Category.comp_id]
  have hn := derivedPullback_normalization (𝟙 X) R K
  dsimp only [EtaleDerivedSectionsPlus.rightDerivedFunctor] at hn
  rw [reassoc_of% hn]
  erw [← (sections X R).rightDerivedFunctorPlusUnit.naturality]
  dsimp only [Functor.comp_map, Functor.id_obj]
  rw [← Functor.map_comp_assoc, sectionsComplexPullback_id]
  simp

/-- The same identity law at every actual bounded-below derived coefficient. -/
@[reassoc] theorem derivedPullback_id
    (K : DerivedCategory.Plus (ModuleSheaf X R)) :
    (derivedPullback (𝟙 X) R).app K ≫
      (EtaleDerivedSectionsPlus.rightDerivedFunctor X R).map
        ((plusFunctorId R X).hom.app K) = 𝟙 _ := by
  simpa using congr_app (derivedPullback_id_eq R (X := X)) K

variable [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wV} (ModuleSheaf V R)]

/-- Successive actual derived section pullbacks as a natural transformation. -/
def compositeDerivedPullback (f : Z ⟶ X) (g : V ⟶ Z) :
    EtaleDerivedSectionsPlus.rightDerivedFunctor X R ⟶
      (plusFunctor f R ⋙ plusFunctor g R) ⋙
        EtaleDerivedSectionsPlus.rightDerivedFunctor V R :=
  derivedPullback f R ≫ Functor.whiskerLeft (plusFunctor f R) (derivedPullback g R) ≫
    (Functor.associator _ _ _).inv

/-- Successive actual derived section pullbacks agree with pullback along the
composite through the constructed geometric coefficient comparison. -/
theorem compositeDerivedPullback_eq (f : Z ⟶ X) (g : V ⟶ Z) :
    compositeDerivedPullback R f g ≫
        Functor.whiskerRight (plusFunctorComp R f g).hom
          (EtaleDerivedSectionsPlus.rightDerivedFunctor V R) =
      derivedPullback (g ≫ f) R := by
  apply Functor.rightDerived_ext (sections X R).rightDerivedFunctorPlus
    (sections X R).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso (ModuleSheaf X R))
  apply NatTrans.ext
  funext K
  dsimp only [compositeDerivedPullback, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.comp_obj, EtaleDerivedSectionsPlus.rightDerivedFunctor]
  simp only [Category.comp_id, Category.assoc]
  apply (cancel_mono ((sections V R).rightDerivedFunctorPlus.map
    ((plusFactors (g ≫ f) R).hom.app K))).mp
  simp only [Category.assoc]
  have hc : (plusFunctorComp R f g).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      (plusFactors (g ≫ f) R).hom.app K =
    (plusFunctor g R).map ((plusFactors f R).hom.app K) ≫
      (plusFactors g R).hom.app ((inverseImage f R).mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Plus.Q.map ((inverseImageComplexComp R f g).hom.app K) := by
    rw [plusFunctorComp_hom_app_Q]
    simp
  rw [← Functor.map_comp, hc, Functor.map_comp, Functor.map_comp]
  have hnat := (derivedPullback g R).naturality ((plusFactors f R).hom.app K)
  dsimp only [EtaleDerivedSectionsPlus.rightDerivedFunctor, Functor.comp_map] at hnat
  rw [← reassoc_of% hnat]
  have hf := derivedPullback_normalization f R K
  have hg := derivedPullback_normalization g R
    ((inverseImage f R).mapCochainComplexPlus.obj K)
  have hh := derivedPullback_normalization (g ≫ f) R K
  dsimp only [EtaleDerivedSectionsPlus.rightDerivedFunctor] at hf hg hh
  rw [reassoc_of% hf, reassoc_of% hg, hh]
  erw [← (sections V R).rightDerivedFunctorPlusUnit.naturality]
  dsimp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    sectionsComplexPullback_comp]

/-- Composition at every actual bounded-below derived coefficient object. -/
@[reassoc] theorem derivedPullback_comp (f : Z ⟶ X) (g : V ⟶ Z)
    (K : DerivedCategory.Plus (ModuleSheaf X R)) :
    (derivedPullback f R).app K ≫
        (derivedPullback g R).app ((plusFunctor f R).obj K) ≫
        (EtaleDerivedSectionsPlus.rightDerivedFunctor V R).map
          ((plusFunctorComp R f g).hom.app K) =
      (derivedPullback (g ≫ f) R).app K := by
  simpa [compositeDerivedPullback] using congr_app (compositeDerivedPullback_eq R f g) K

end Langlands.Geometry.EtaleDerivedGlobalPullback
