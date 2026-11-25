/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface

/-! # Shared derived quotient, evaluation and boundary constructions

Source: diagonal limit (3).
(blueprint: def-diagonal-cyclic-quotient-functors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

/-- Completed quotient followed by evaluation, shared as one actual functor.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-quotient-functors). -/
@[irreducible] def cyclicCompletedQuotient (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted l W)]
    (M : DiagonalCompletedReduction l W) (n : ℕ) :
    DerivedCategory.{u + 1} (DiagonalCompleted l W) ⥤
      DerivedCategory.{u + 1} (DiagonalCompleted l W) :=
  M.derived.T ⋙ ((evaluation ℕᵒᵖ
    (DiagonalCompleted l W)).obj (op n)).mapDerivedCategory

/-- Derived discrete restriction, shared before inserting quotient objects.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-quotient-functors). -/
@[irreducible] def cyclicDiscreteRestriction (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l W)]
    [HasDerivedCategory.{u + 1} (DiagonalMod l W)] :
    DerivedCategory.{u + 1} (DiagonalCompleted l W) ⥤
      DerivedCategory.{u + 1} (DiagonalMod l W) :=
  (diagonalCompletedRestriction l W).mapDerivedCategory

/-- Derived evaluation at one coefficient level.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-quotient-functors). -/
@[irreducible] def cyclicSystemEvaluation (l : ℕ) [Fact l.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalMod l W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems l W)] (n : ℕ) :
    DerivedCategory.{u + 1} (DiagonalSystems l W) ⥤
      DerivedCategory.{u + 1} (DiagonalMod l W) :=
  ((evaluation ℕᵒᵖ (DiagonalMod l W)).obj (op n)).mapDerivedCategory

/-- The actual strict-system image of the integral boundary, shared as one arrow.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-quotient-functors).
This is functorial application to the given boundary, with no class chosen. -/
@[irreducible] def cyclicStrictBoundary (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y))]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y))) :
    D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ⟶
      D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
        (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) :=
  D.T.map (diagonalIntegralBoundary Y).hom

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
