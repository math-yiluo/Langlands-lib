/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Sites.EtalePicard
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundary
/-!
# Relative supported Cartier Kummer boundary

## Main definitions

* `supportedDivisorSection`: the section dual to the ideal inclusion.
* `SupportedKummerBoundary`: the normalized relative torsor-extension boundary.
* `supportedConstantExchange`: the canonical closed exchange on constants.

## References

* Stacks Project, Tags 03PL and 0A45
* Stacks 0A45, base change
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical closed-immersion exchange on the constant sheaf. -/
def supportedConstantExchange (A : Type (u + 1)) [CommRing A]
    {D D' T T' : Scheme.{u}} (i : D ⟶ T) (i' : D' ⟶ T')
    (v : T' ⟶ T) (w : D' ⟶ D) (sq : CommSq w i' i v) :
    (upperStar (ModuleCat.{u + 1} A) v).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i').obj (ordinaryFiniteConstant A D') :=
  (baseChangeMap (ModuleCat.{u + 1} A) sq).app (ordinaryFiniteConstant A D) ≫
    (lowerStar (ModuleCat.{u + 1} A) i').map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) w).app
        (ModuleCat.of A A)).hom

end AlgebraicGeometry.Etale
