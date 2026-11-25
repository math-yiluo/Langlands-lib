/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalTraceCompletedSupportedUnit
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteChernComposite
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceProjectionEquations

/-! # The finite completed Chern equation with shared endpoints -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap
  Coefficients.lineMap Coefficients.unitMap

/-- Exactly the finite completed diagonal Chern equality, with its category
interfaces shared before the strict comparison argument. This is a definition of
the equality, not an assertion that it holds.
Source: diagonal trace proof (2), forgetting the support of the diagonal.
(blueprint: def-sfb-diagonal-trace-finite-chern-equation). -/
@[irreducible]
def finiteChernEquation (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) (n : ℕ)
    (delta : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y) : Prop :=
  let U := diagonalCompletedUnderlying l (diagonalSurface Y)
  let V := r.F.mapDerivedCategory
  completedBoundaryEquation U
    ((DerivedCategory.singleFunctor (DiagonalCompleted l (diagonalSurface Y)) 0).map
      (completedSupportedUnit l Y)) delta
    (shiftedComparison U (V ⋙ L.R) (k.lineMap l (ULift.{u} (Padic l)) L) 2 ≫
      (L.projection n).app _)
    (finiteChernComposite l (diagonalSurface Y) c r k L n (SpTowerClasses.diagonalPic Y))

end AlgebraicGeometry.ProEtale.DiagonalTrace
