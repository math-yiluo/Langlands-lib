/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import all Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantPullbackHom
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# The ordinary constant pullback component
-/
@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
attribute [local irreducible] DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar

/-- The ordinary single-iso factorization is the canonical constant comparison.
Source: blueprint thm-amb-p1-adjunction.proof.md, canonical constant coefficient pullback.
Expand the two component formulas, which are the same single-degree comparison
followed by the single functor applied to the constant-sheaf comparison.
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteUnitPullback_hom_eq_constant (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFiniteUnitPullback A f).hom =
      (constantSinglePullbackIso (ModuleCat.{u + 1} A) f (ModuleCat.of A A)).hom := by
  exact (ordinaryFiniteUnitPullback_hom A f).trans (ordinaryFiniteConstantPullback_hom A f).symm

end AlgebraicGeometry.Etale
