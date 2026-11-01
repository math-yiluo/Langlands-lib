import Langlands.Geometry.EtaleDerivedInverseImage
import Langlands.Geometry.EtaleDerivedDirectImage
import Langlands.Cohomology.AdditiveAdjunction
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # The actual bounded-below geometric derived adjunction -/

noncomputable section

universe u wX wZ

namespace Langlands.Geometry.EtaleDerivedAdjunction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDirectImage EtaleDerivedSections
open EtaleDerivedInverseImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]

/-- The actual geometric adjunction applied termwise, restricted to bounded-below
complexes through the fully faithful complex inclusions. -/
def complexPlusAdjunction :
    (inverseImage f R).mapCochainComplexPlus ⊣ (EtaleDirectImage.directImage f (ModuleCat.{u} R)).mapCochainComplexPlus :=
  (Langlands.Cohomology.complexAdjunction (inverseImageAdjunction f R) (.up ℤ)).restrictFullyFaithful
      (CochainComplex.Plus.fullyFaithfulι (ModuleSheaf X R))
      (CochainComplex.Plus.fullyFaithfulι (ModuleSheaf Z R))
      (inverseImage f R).mapCochainComplexPlusCompι.symm
      (EtaleDirectImage.directImage f (ModuleCat.{u} R)).mapCochainComplexPlusCompι.symm

private instance inverse_isLeftDerivedFunctor :
    (plusFunctor f R).IsLeftDerivedFunctor (plusFactors f R).hom
      (CochainComplex.Plus.quasiIso (ModuleSheaf X R)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ (plusFactors f R)

private instance inverse_postcomp_isLeftDerivedFunctor
    (G : DerivedCategory.Plus (ModuleSheaf Z R) ⥤ DerivedCategory.Plus (ModuleSheaf X R)) :
    (plusFunctor f R ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight (plusFactors f R).hom G)
      (CochainComplex.Plus.quasiIso (ModuleSheaf X R)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (plusFactors f R) G)

private instance direct_postcomp_isRightDerivedFunctor :
    ((EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlus ⋙ plusFunctor f R).IsRightDerivedFunctor
      (Functor.whiskerRight (EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit (plusFunctor f R) ≫
        (Functor.associator _ _ _).hom)
      (CochainComplex.Plus.quasiIso (ModuleSheaf Z R)) := by
  have h : (CochainComplex.Plus.localizerMorphism (ModuleSheaf Z R)).Derives
      ((EtaleDirectImage.directImage f (ModuleCat.{u} R)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ plusFunctor f R) := by
    intro K L a ha
    have : IsIso (((EtaleDirectImage.directImage f (ModuleCat.{u} R)).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map
        ((InjectiveObject.ι (ModuleSheaf Z R)).mapCochainComplexPlus.map a)) :=
      CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus
        (EtaleDirectImage.directImage f (ModuleCat.{u} R)) a ha
    change IsIso ((plusFunctor f R).map
      (((EtaleDirectImage.directImage f (ModuleCat.{u} R)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q).map
          ((InjectiveObject.ι (ModuleSheaf Z R)).mapCochainComplexPlus.map a)))
    infer_instance
  exact h.isRightDerivedFunctor_of_isIso _ (fun K => by
    dsimp
    infer_instance)

/-- The constructed exact inverse image on Dplus is left adjoint to the actual
right-derived geometric direct image. -/
def adjunction :
    plusFunctor f R ⊣ EtaleDerivedDirectImage.rightDerivedFunctor f R := by
  change plusFunctor f R ⊣
    (EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlus
  exact (complexPlusAdjunction f R).derived
    (CochainComplex.Plus.quasiIso (ModuleSheaf X R))
    (CochainComplex.Plus.quasiIso (ModuleSheaf Z R))
    (plusFactors f R).hom (EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit

instance inverse_isLeftAdjoint : (plusFunctor f R).IsLeftAdjoint :=
  (adjunction f R).isLeftAdjoint

instance direct_isRightAdjoint :
    (EtaleDerivedDirectImage.rightDerivedFunctor f R).IsRightAdjoint :=
  (adjunction f R).isRightAdjoint

/-- The derived unit is normalized by the actual termwise unit and the
right-derived direct-image comparison. -/
@[reassoc] theorem unit_app_Q (K : CochainComplex.Plus (ModuleSheaf X R)) :
    (adjunction f R).unit.app (DerivedCategory.Plus.Q.obj K) ≫
        (EtaleDerivedDirectImage.rightDerivedFunctor f R).map
          ((plusFactors f R).hom.app K) =
      DerivedCategory.Plus.Q.map ((complexPlusAdjunction f R).unit.app K) ≫
        (EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit.app
          ((inverseImage f R).mapCochainComplexPlus.obj K) :=
  (complexPlusAdjunction f R).derivedη_fac_app
    (CochainComplex.Plus.quasiIso (ModuleSheaf X R))
    (plusFactors f R).hom
    (EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit K

/-- The derived counit is normalized by the actual termwise counit. -/
@[reassoc] theorem counit_app_Q (K : CochainComplex.Plus (ModuleSheaf Z R)) :
    (plusFunctor f R).map
        ((EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit.app K) ≫
        (adjunction f R).counit.app (DerivedCategory.Plus.Q.obj K) =
      (plusFactors f R).hom.app
          ((EtaleDirectImage.directImage f (ModuleCat.{u} R)).mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Plus.Q.map ((complexPlusAdjunction f R).counit.app K) :=
  (complexPlusAdjunction f R).derivedε_fac_app
    (CochainComplex.Plus.quasiIso (ModuleSheaf Z R))
    (plusFactors f R).hom
    (EtaleDirectImage.directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlusUnit K

instance direct_additive :
    (EtaleDerivedDirectImage.rightDerivedFunctor f R).Additive :=
  (adjunction f R).right_adjoint_additive

instance direct_linear :
    (EtaleDerivedDirectImage.rightDerivedFunctor f R).Linear R where
  map_smul a r := ((adjunction f R).homEquiv _ _).symm.injective (by
    simp [Adjunction.homEquiv_counit])

/-- The actual derived Hom correspondence retains coefficient linearity. -/
def homLinearEquiv (K : DerivedCategory.Plus (ModuleSheaf X R))
    (L : DerivedCategory.Plus (ModuleSheaf Z R)) :
    ((plusFunctor f R).obj K ⟶ L) ≃ₗ[R]
      (K ⟶ (EtaleDerivedDirectImage.rightDerivedFunctor f R).obj L) :=
  { (adjunction f R).homAddEquiv K L with
    map_smul' := by
      intro r a
      simp [Adjunction.homEquiv_unit] }

@[simp] theorem homLinearEquiv_apply (K : DerivedCategory.Plus (ModuleSheaf X R))
    (L : DerivedCategory.Plus (ModuleSheaf Z R))
    (a : (plusFunctor f R).obj K ⟶ L) :
    homLinearEquiv f R K L a = (adjunction f R).unit.app K ≫
      (EtaleDerivedDirectImage.rightDerivedFunctor f R).map a :=
  (adjunction f R).homEquiv_unit K L a

@[simp] theorem homLinearEquiv_symm_apply (K : DerivedCategory.Plus (ModuleSheaf X R))
    (L : DerivedCategory.Plus (ModuleSheaf Z R))
    (a : K ⟶ (EtaleDerivedDirectImage.rightDerivedFunctor f R).obj L) :
    (homLinearEquiv f R K L).symm a =
      (plusFunctor f R).map a ≫ (adjunction f R).counit.app L :=
  (adjunction f R).homEquiv_counit K L a

end Langlands.Geometry.EtaleDerivedAdjunction
