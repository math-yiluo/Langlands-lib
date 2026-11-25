/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDirectCompositorCoordinatesMatePasting

/-! # Coefficient realization of an ordinary direct-image compositor

## References

* Stacks 00YV and 03D3 (transport of the module adjunction), 07A5 and 07A6 (K-injective direct image
  and its adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

/-- The section-normalized coefficient realization preserves the ordinary direct-image
compositor. This is solely a comparison between the two presentations of one finite
coefficient category: it involves no coefficient sequence, evaluation, or system operation.
-/
theorem sfIntrinsicDirectCompositorCoordinates_kInjective
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) [I.IsKInjective] :
    let B := ModuleCat.{u + 1} (ULift.{u + 1} A)
    let af := (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction
    let ag := (sfIntrinsicConstantModuleAdjunction g A).mapDerivedCategoryRightDerivedAdjunction
    let adjt := (sfIntrinsicConstantModuleAdjunction
      (f ≫ g) A).mapDerivedCategoryRightDerivedAdjunction
    (proEtaleConstantDerivedDirectImage g A).map
        ((sfIntrinsicDerivedDirectImageComparison f A).hom.app (DerivedCategory.Q.obj I)) ≫
      (sfIntrinsicDerivedDirectImageComparison g A).hom.app
        ((lowerStar B f).rightDerivedFunctor.obj (DerivedCategory.Q.obj I)) ≫
      (sfIntrinsicDerivedEquivalence Z A).functor.map
        ((conjugateIsoEquiv
          ((derivedUpperStarLowerStarAdjunction B g).comp
            (derivedUpperStarLowerStarAdjunction B f))
          (derivedUpperStarLowerStarAdjunction B (f ≫ g))
          (leftDerivedUpperStarComp B f g)).hom.app (DerivedCategory.Q.obj I)) =
    (conjugateIsoEquiv (ag.comp af) adjt
      (sfIntrinsicDerivedPullbackComp A f g)).hom.app
        ((sfIntrinsicDerivedEquivalence X A).functor.obj (DerivedCategory.Q.obj I)) ≫
      (sfIntrinsicDerivedDirectImageComparison (f ≫ g) A).hom.app
        (DerivedCategory.Q.obj I) := by
  calc
    _ = sfIntrinsicAmbientIntermediate A f g I :=
      sfIntrinsicDirectCompositorCoordinates_ambient_normalization A f g I
    _ = _ := sfIntrinsicDirectCompositorCoordinates_ambient_to_intrinsic A f g I

end AlgebraicGeometry.Scheme
