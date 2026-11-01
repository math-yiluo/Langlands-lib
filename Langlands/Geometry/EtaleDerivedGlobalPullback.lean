import Langlands.Geometry.EtaleDerivedAdjunction

/-! # Derived global sections and pullback for arbitrary scheme morphisms -/

noncomputable section

universe u wX wZ wR

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Actual geometric direct image restricted to the full injective subcategories. -/
def directImageInjectives : InjectiveObject (ModuleSheaf Z R) ⥤
    InjectiveObject (ModuleSheaf X R) :=
  ObjectProperty.lift _
    (InjectiveObject.ι (ModuleSheaf Z R) ⋙
      EtaleDirectImage.directImage f (ModuleCat.{u} R)) (fun J => by
        exact (EtaleDirectImage.directImage f (ModuleCat.{u} R)).injective_obj_of_injective
          J.property)

instance directImageInjectives_additive : (directImageInjectives f R).Additive := by
  dsimp only [directImageInjectives]
  infer_instance

/-- The right-derived section comparison is invertible on the actual direct
image of each bounded-below injective complex. -/
instance sectionUnit_directImage_injectiveComplex
    (K : CochainComplex.Plus (InjectiveObject (ModuleSheaf Z R))) :
    IsIso ((sections X R).rightDerivedFunctorPlusUnit.app
      ((EtaleDirectImage.directImage f (ModuleCat.{u} R)).mapCochainComplexPlus.obj
        ((InjectiveObject.ι (ModuleSheaf Z R)).mapCochainComplexPlus.obj K))) := by
  change IsIso ((sections X R).rightDerivedFunctorPlusUnit.app
    ((InjectiveObject.ι (ModuleSheaf X R)).mapCochainComplexPlus.obj
      ((directImageInjectives f R).mapCochainComplexPlus.obj K)))
  infer_instance

/-- The actual terminal/global-section comparison applied termwise to
bounded-below complexes, naturally in every complex map. -/
def sectionsComplexIso :
    (EtaleDirectImage.directImage f (ModuleCat.{u} R)).mapCochainComplexPlus ⋙
        (sections X R).mapCochainComplexPlus ≅
      (sections Z R).mapCochainComplexPlus :=
  NatIso.ofComponents (fun K =>
    (CochainComplex.Plus.ι (ModuleCat.{u} R)).preimageIso
      ((Functor.mapHomologicalComplexCompIso
        (EtaleDerivedDirectImage.directImageSectionsIso f R) (.up ℤ)).app K.obj))
    (fun {_K _L} a => by
      apply (CochainComplex.Plus.ι (ModuleCat.{u} R)).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (Functor.mapHomologicalComplexCompIso
        (EtaleDerivedDirectImage.directImageSectionsIso f R) (.up ℤ)).hom.naturality a.hom)

/-- The canonical comparison from original global-section complexes to the
composite of the two actual right-derived functors. -/
def compositeUnit :
    (sections Z R).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶
      DerivedCategory.Plus.Q ⋙
        ((EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlus ⋙
          (sections X R).rightDerivedFunctorPlus) :=
  (Functor.isoWhiskerRight (sectionsComplexIso f R) DerivedCategory.Plus.Q).inv ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (sections X R).rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit _ ≫
    (Functor.associator _ _ _).hom

instance composite_isRightDerivedFunctor :
    ((EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlus ⋙
      (sections X R).rightDerivedFunctorPlus).IsRightDerivedFunctor
      (compositeUnit f R) (CochainComplex.Plus.quasiIso (ModuleSheaf Z R)) := by
  apply (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus
    (sections Z R)).isRightDerivedFunctor_of_isIso
  intro K
  change IsIso ((compositeUnit f R).app
    ((InjectiveObject.ι (ModuleSheaf Z R)).mapCochainComplexPlus.obj K))
  simp only [compositeUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  infer_instance

/-- Derived sections of actual derived geometric direct image are canonically
identified with derived sections on the source scheme. -/
def directImageSectionsIso :
    EtaleDerivedDirectImage.rightDerivedFunctor f R ⋙
        EtaleDerivedSectionsPlus.rightDerivedFunctor X R ≅
      EtaleDerivedSectionsPlus.rightDerivedFunctor Z R := by
  change (EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlus ⋙
    (sections X R).rightDerivedFunctorPlus ≅ (sections Z R).rightDerivedFunctorPlus
  exact Functor.rightDerivedUnique _ _ (compositeUnit f R)
    (sections Z R).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso (ModuleSheaf Z R))

/-- The constructed section comparison is normalized by the actual
right-derived units on every complex representative. -/
@[reassoc] theorem directImageSectionsIso_unit
    (K : CochainComplex.Plus (ModuleSheaf Z R)) :
    (compositeUnit f R).app K ≫
        (directImageSectionsIso f R).hom.app (DerivedCategory.Plus.Q.obj K) =
      (sections Z R).rightDerivedFunctorPlusUnit.app K := by
  simpa only [directImageSectionsIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso, id_eq, EtaleDerivedSectionsPlus.rightDerivedFunctor,
    EtaleDerivedDirectImage.rightDerivedFunctor, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] using
    Functor.rightDerivedNatTrans_app _ _ (compositeUnit f R)
    (sections Z R).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso (ModuleSheaf Z R)) (𝟙 _) K

/-- The derived adjunction unit defines actual pullback of derived global
sections for every bounded-below derived sheaf. -/
def derivedPullback :
    EtaleDerivedSectionsPlus.rightDerivedFunctor X R ⟶
      EtaleDerivedInverseImage.plusFunctor f R ⋙
        EtaleDerivedSectionsPlus.rightDerivedFunctor Z R :=
  (EtaleDerivedSectionsPlus.rightDerivedFunctor X R).leftUnitor.inv ≫
    Functor.whiskerRight (EtaleDerivedAdjunction.adjunction f R).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (directImageSectionsIso f R).hom

theorem derivedPullback_app (K : DerivedCategory.Plus (ModuleSheaf X R)) :
    (derivedPullback f R).app K =
      (EtaleDerivedSectionsPlus.rightDerivedFunctor X R).map
          ((EtaleDerivedAdjunction.adjunction f R).unit.app K) ≫
        (directImageSectionsIso f R).hom.app
          ((EtaleDerivedInverseImage.plusFunctor f R).obj K) := by
  simp [derivedPullback]

/-- The derived map specialized to an actual coefficient sheaf in degree zero. -/
def sheafDerivedPullback :
    EtaleDerivedSectionsPlus.derivedSections X R ⟶
      inverseImage f R ⋙ EtaleDerivedSectionsPlus.derivedSections Z R :=
  Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) 0)
      (derivedPullback f R) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (EtaleDerivedInverseImage.plusSingleIso f R 0).hom _ ≫
    (Functor.associator _ _ _).hom

/-- Actual ordinary small-etale cohomology pullback in every nonnegative degree,
natural in the coefficient sheaf. -/
def cohomologyPullback (q : ℕ) :
    cohomology X R q ⟶ inverseImage f R ⋙ cohomology Z R q :=
  (EtaleDerivedSectionsPlus.homologyNatIso X R q).inv ≫
    Functor.whiskerRight (sheafDerivedPullback f R)
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (inverseImage f R)
      (EtaleDerivedSectionsPlus.homologyNatIso Z R q).hom

@[reassoc] theorem cohomologyPullback_naturality (q : ℕ)
    {F G : ModuleSheaf X R} (a : F ⟶ G) :
    (cohomology X R q).map a ≫ (cohomologyPullback f R q).app G =
      (cohomologyPullback f R q).app F ≫
        (cohomology Z R q).map ((inverseImage f R).map a) :=
  (cohomologyPullback f R q).naturality a

end Langlands.Geometry.EtaleDerivedGlobalPullback
