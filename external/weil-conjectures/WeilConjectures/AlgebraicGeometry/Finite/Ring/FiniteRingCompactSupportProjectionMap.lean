/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Compact-support projection with arbitrary finite primary coefficients

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-compatibilities.proof.md`, Proof (3); Stacks Project, Tag 0F0G
(blueprint: def-sp-finite-ring-compact-support-projection-map).

The canonical coefficient realization changes only the presentation of module sheaves.
The projection arrow below is the published counit-defined compactification projection
transported by that realization, on the ordinary unbounded intrinsic derived categories.
-/

@[expose] public section

set_option autoImplicit false

-- Keep lifted coefficient instances on the commutative-ring projection.
attribute [local instance 2000] CommRing.toRing
attribute [local instance 2000] isNoetherian_of_finite

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-! Named instance proofs keep the ULift coefficient and realization arguments atomic.
Without these shortcuts Lean abstracts the constructed proofs separately in the map and
in its users, and comparing the derived tensor expressions can exceed the compile limit.
All statements below are existing instances; no additional hypotheses or data are introduced.
Source: the imported Mathlib and fixed-coefficient instances
(blueprint: def-sp-finite-ring-compact-support-projection-map). -/

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_moduleSheafify (R : Type u) [CommRing R] {X : Scheme.{u}} :
    HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_sheafGroth (R : Type u) [CommRing R] {X : Scheme.{u}} :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} R))) := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_functorLimits (R : Type u) [CommRing R] [Finite R]
    {X : Scheme.{u}} :
    PreservesFiniteLimits (sfIntrinsicModuleEquivalence X R).functor := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_functorColimits (R : Type u) [CommRing R] [Finite R]
    {X : Scheme.{u}} :
    PreservesFiniteColimits (sfIntrinsicModuleEquivalence X R).functor := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_inverseAdditive (R : Type u) [CommRing R] [Finite R]
    {X : Scheme.{u}} :
    (sfIntrinsicModuleEquivalence X R).inverse.Additive := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_inverseLimits (R : Type u) [CommRing R] [Finite R]
    {X : Scheme.{u}} :
    PreservesFiniteLimits (sfIntrinsicModuleEquivalence X R).inverse := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_inverseColimits (R : Type u) [CommRing R] [Finite R]
    {X : Scheme.{u}} :
    PreservesFiniteColimits (sfIntrinsicModuleEquivalence X R).inverse := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_moduleGroth (R : Type u) [CommRing R] :
    IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_modulePreadditive (R : Type u) [CommRing R] :
    MonoidalPreadditive (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_moduleFlat (R : Type u) [CommRing R] :
    Abelian.HasFunctorialFlatResolution
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

/-- Atomic instance proof for the canonical coefficient transport. -/
theorem finiteProjection_upperFlat (R : Type u) [CommRing R] [Finite R] :
    ProEtale.UpperStarPreservesFlat
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) := inferInstance

attribute [local instance 10000] WeilConjectures.sfAbBijective WeilConjectures.sfAbSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat

/-- The specified compact-support projection arrow in intrinsic constant-ring modules.
The fixed-scalar arrow is the counit-defined proper projection, followed by the inverse
open projection and the pullback-composition identification. Apply the canonical derived
realization after evaluating it on the inverse realizations of `M,K`. In particular this
is a natural transformation, with no chosen projection-formula isomorphism or Tor assumption.
Naturality in both arguments is inherited from the published natural transformation.
Source: blueprint Proof (3), tensor-map paragraph; Stacks Tag 0F0G
(blueprint: def-sp-finite-ring-compact-support-projection-map). -/
noncomputable def finiteRingCompactSupportProjection
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (Functor.postcompose₂.obj
    (sfIntrinsicModuleEquivalence Y R).functor.mapDerivedCategory).map
      (((((Functor.whiskeringLeft₂ _).obj
        (sfIntrinsicModuleEquivalence X R).inverse.mapDerivedCategory).obj
          (sfIntrinsicModuleEquivalence Y R).inverse.mapDerivedCategory)).map
            (ProEtale.projectionMapOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c))

end AlgebraicGeometry.Scheme
