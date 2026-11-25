/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import all Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.EtaleSectionUnitNormalization
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# The canonical constant pullback unit square
-/
@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
attribute [local irreducible] DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar

/-- The canonical constant pullback preserves the module coefficient unit.
Source: blueprint thm-amb-p1-adjunction.proof.md, constant coefficient normalization.
Specialize the proved canonical constant-complex unit square to module coefficients;
the coefficient monoidal unit is the module A itself.
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteConstantUnit_square (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (constantSinglePullbackIso (ModuleCat.{u + 1} A) f (ModuleCat.of A A)).hom ≫
        (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).hom =
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom ≫
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom := by
  exact (constantUnitPullback_unit (ModuleCat.{u + 1} A) f).symm

end AlgebraicGeometry.Etale
