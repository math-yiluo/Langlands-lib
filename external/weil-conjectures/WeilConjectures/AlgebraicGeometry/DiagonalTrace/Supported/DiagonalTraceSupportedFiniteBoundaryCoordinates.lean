/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteCoordinateEquation
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedFiniteBoundaryEquation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierMapCoordinates

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

/-- Convert finite coordinates to the named supported Cartier equation.
Source: diagonal trace proof (2), finite source projection.
(blueprint: lem-sfb-diagonal-trace-supported-finite-boundary-coordinate-conversion).

Proof: expand the named coordinate and supported boundary predicates. The source
comparison, root transport, coefficient unit map and finite Cartier map contain
precisely the same single, shift and projection composites. Expanding the canonical
finite Cartier class and the unit/line aliases identifies both equations. -/
theorem diagonalTrace_supportedFiniteBoundary_of_coordinates
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
    (hb : supportedFiniteCoordinateEquation l Y hY D H s c r k e p L₀ L n a a.line) :
    supportedFiniteBoundaryCartierEquation l Y hY D H s c r k e p L₀ L n a := by
  unfold supportedFiniteCoordinateEquation finiteBoundaryCoordinateEquation at hb
  unfold supportedFiniteBoundaryCartierEquation
  have hmap := supportedFiniteCartierMap_coordinates l Y hY c r k n a L
  unfold finiteCartierCoordinateMapEquation at hmap
  rw [hmap]
  unfold supportedBoundaryEquation supportedSourceComparison coefficientRootTransport
  dsimp only [diagonalCompletedUnderlying, completedUnit,
    SpTowerClasses.unit, SpTowerClasses.line]
  exact hb

end AlgebraicGeometry.ProEtale.DiagonalTrace
