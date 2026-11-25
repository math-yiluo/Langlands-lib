/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryMaps
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteBoundarySourceAlgebra
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierArrow

/-! # Coordinates for the finite supported boundary equation -/

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
  diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  diagonalSingleLimitComparison diagonalExactFunctorExtImage
  diagonalShiftedSingleLimitComparison diagonalCompletedGenerator
  SpTowerClasses.lineModule Coefficients.unitMap
  completedSupportedUnit

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The expanded finite coordinate equation, with all concrete categorical structures shared.
Source: diagonal trace proof (2), finite source projection.
(blueprint: def-sfb-diagonal-trace-supported-finite-coordinate-equation). -/
@[irreducible] def supportedFiniteCoordinateEquation
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
        (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y)))
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (e : H ≅ r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c))
    (p : ExtDerivedPresentation (D.E.obj (diagonalIntegralSource Y)) H)
    (L₀ L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) (n : ℕ)
    (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (b : (r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c)).obj (op n) ≅
      (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
        (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
          (cartierResidue_cast l (n + 1)) (diagonalSurface Y)))
    : Prop :=
  finiteBoundaryCoordinateEquation
    (diagonalCompletedRestriction l (diagonalSurface Y)) r.F
    (completedSupportedUnit l Y) p s L₀ L
    (SpTowerClasses.coefficient (diagonalSurface Y)
      (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))
    (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c) e n a.coefficient
    k.coefficientProjection
    ((diagonalFiniteToPadic l n (diagonalSurface Y)).map
      (Scheme.proEtaleConstantDirectImageMap (diagonalImmersion Y)
        (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
        (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n))))
    (finiteCartierArrow l Y hY n) b

end AlgebraicGeometry.ProEtale.DiagonalTrace
