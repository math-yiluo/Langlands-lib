/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedSourceComparison
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalTraceCompletedSupportedUnit
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceRootTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceProjectionEquations
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteChernComposite

/-! # The finite supported boundary equation with shared endpoint types -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  diagonalSingleLimitComparison diagonalExactFunctorExtImage
  diagonalShiftedSingleLimitComparison diagonalCompletedGenerator
  SpTowerClasses.lineModule Coefficients.unitMap

/-- The finite supported boundary equation, with its concrete endpoints checked once.
This is exactly the projected supported-class composite equal to the projected
coefficient Chern composite; it asserts no normalization by itself.
Source: diagonal trace proof (2), the finite Cartier/Chern equation.
(blueprint: def-sfb-diagonal-trace-finite-boundary-equation). -/
@[irreducible]
def finiteBoundaryEquation
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (p : ExtDerivedPresentation (D.E.obj (diagonalIntegralSource Y)) H)
    (s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y)))
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (e : H ≅ r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c))
    (L₀ L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) (n : ℕ) : Prop :=
    let U := diagonalCompletedUnderlying l (diagonalSurface Y)
    let ev := ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
      (op n)).mapDerivedCategory
    supportedBoundaryEquation U L₀.R ev (L₀.projection n)
      ((DerivedCategory.singleFunctor _ 0).map (completedSupportedUnit l Y))
      (supportedSourceComparison l Y D p s L₀)
      p.arrow (coefficientRootTransport l (diagonalSurface Y) c r p.target e).hom
      (finiteChernComposite l (diagonalSurface Y) c r k L n
        (SpTowerClasses.diagonalPic Y))

end AlgebraicGeometry.ProEtale.DiagonalTrace
