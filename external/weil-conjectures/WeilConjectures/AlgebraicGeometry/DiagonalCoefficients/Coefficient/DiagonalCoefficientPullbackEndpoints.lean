/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientExchange

/-! # Canonical pullback of diagonal coefficient diagrams

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-pullback-endpoints).

## Main definitions

- `PullEndpoint`: the ordinary module endpoint fixed by its underlying adjoint.
- `PullEndpoint.derived`, `PullEndpoint.shift`: its canonical derived arrows.
- `modelExchange`, `TracePullback`: the normalized derived trace comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- A module pullback endpoint is fixed by the actual inverse-image map on
underlying sheaves, through the ordinary module adjunction. Source: blueprint
clause 3 (blueprint: def-sfb-diagonal-coefficient-pullback-endpoints). -/
structure PullEndpoint (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S)
    (M : Modules R S) (N : Modules R X)
    (m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X) where
  iso : (CondensedRing.upperStar R f).obj M ≅ N
  normalization :
    (((CondensedRing.upperStarLowerStarAdjunction R f).homEquiv _ _) iso.hom).hom =
      (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _ m

/-- The coefficient-unit endpoint under its actual condensed pullback map.
This names its fixed regular-module parameters once.
Source: blueprint base-change unit normalization
(blueprint: def-sfb-diagonal-coefficient-pullback-endpoints). -/
def UnitPullEndpoint (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) :=
  PullEndpoint R f (Mod.regular (condensedRingObj R S))
    (Mod.regular (condensedRingObj R X)) (condensedPullbackHom R f)

/-- The canonical exact inverse-image comparison on a degree-zero module.
Naming its component fixes both categories before elaborating any geometric
supported-source expression. Source: blueprint base-change identifications
(blueprint: def-sfb-diagonal-coefficient-pullback-endpoints). -/
def singlePullback (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} (f : X ⟶ S) (M : Modules R S) :
    (derivedUpper R f).obj ((DerivedCategory.singleFunctor (Modules R S) 0).obj M) ≅
      (DerivedCategory.singleFunctor (Modules R X) 0).obj
        ((CondensedRing.upperStar R f).obj M) :=
  (Functor.singleFunctorCompLeftDerivedFunctorIso (CondensedRing.upperStar R f)).app M

/-- The exact pullback single comparison followed by the normalized endpoint.
Source: blueprint clause 3 (blueprint: def-sfb-diagonal-coefficient-pullback-endpoints). -/
def PullEndpoint.derived {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} {f : X ⟶ S}
    {M : Modules R S} {N : Modules R X}
    {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (e : PullEndpoint R f M N m) :
    (derivedUpper R f).obj
      ((DerivedCategory.singleFunctor (Modules R S) 0).obj M) ⟶
        (DerivedCategory.singleFunctor (Modules R X) 0).obj N :=
  (singlePullback R f M).hom ≫
    (DerivedCategory.singleFunctor (Modules R X) 0).map e.iso.hom

/-- The shifted exact-pullback endpoint uses its canonical shift comparison.
Source: blueprint clause 3 (blueprint: def-sfb-diagonal-coefficient-pullback-endpoints). -/
def PullEndpoint.shift {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {X S : Scheme.{u}} {f : X ⟶ S}
    {M : Modules R S} {N : Modules R X}
    {m : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X}
    (e : PullEndpoint R f M N m) :
    (derivedUpper R f).obj
      (((DerivedCategory.singleFunctor (Modules R S) 0).obj M)⟦(2 : ℤ)⟧) ⟶
        ((DerivedCategory.singleFunctor (Modules R X) 0).obj N)⟦(2 : ℤ)⟧ :=
  ((derivedUpper R f).commShiftIso (2 : ℤ)).hom.app _ ≫
    e.derived⟦(2 : ℤ)⟧'

/-- The direct-image comparison evaluated in universally specified models of
right derivation, conjugated only by their equalities to the canonical functors.
Source: blueprint clause 3 (blueprint: def-sfb-diagonal-coefficient-pullback-endpoints). -/
def modelExchange (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (D : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar R f'))
    (e : D.R = (derivedLower R f))
    (e' : D'.R = (derivedLower R f'))
    (K : DerivedCategory (Modules R X)) :
    (derivedUpper R hS).obj (D.R.obj K) ⟶
      D'.R.obj ((derivedUpper R hX).obj K) :=
  (derivedUpper R hS).map ((eqToIso e).hom.app K) ≫
    (derivedExchange R f f' hX hS h).app K ≫
    (eqToIso e').inv.app _

/-- One trace's base-change equation under the specified canonical mate.
Source: blueprint clause 3 (blueprint: def-sfb-diagonal-coefficient-pullback-endpoints). -/
def TracePullback (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (D : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar R f'))
    (e : D.R = (derivedLower R f))
    (e' : D'.R = (derivedLower R f'))
    {L : Modules R X} {L' : Modules R X'}
    {m : (upperStar Ab.{u + 1} hX).obj L.X ⟶ L'.X}
    (line : PullEndpoint R hX L L' m)
    (c : PullEndpoint R hS (Mod.regular (condensedRingObj R S))
      (Mod.regular (condensedRingObj R S')) (condensedPullbackHom R hS))
    (t : D.R.obj (((DerivedCategory.singleFunctor (Modules R X) 0).obj L)⟦(2 : ℤ)⟧) ⟶ unit R S)
    (t' : D'.R.obj (((DerivedCategory.singleFunctor (Modules R X') 0).obj L')⟦(2 : ℤ)⟧) ⟶
      unit R S') : Prop :=
  IsIso (modelExchange R f f' hX hS h D D' e e'
    (((DerivedCategory.singleFunctor (Modules R X) 0).obj L)⟦(2 : ℤ)⟧)) ∧
    (derivedUpper R hS).map t ≫ c.derived =
      modelExchange R f f' hX hS h D D' e e' _ ≫ D'.R.map line.shift ≫ t'

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
