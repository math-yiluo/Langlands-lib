/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierCoordinateEquation
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierArrow
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierArrowHom
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierMapExpansion

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

/-- The published finite Cartier map is the generic finite coordinate composite.
Source: diagonal trace proof (2), finite Cartier endpoint.
(blueprint: lem-sfb-diagonal-trace-finite-cartier-map-coordinates).
Proof: specialize the expansion to the canonical Cartier class. Its exact image is
finiteCartierClass, whose Hom is the named finiteCartierArrow. -/
theorem supportedFiniteCartierMap_coordinates
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) :
    finiteCartierCoordinateMapEquation l Y hY c r k n a L := by
  unfold finiteCartierCoordinateMapEquation
  rw [finiteCartierArrow_hom]
  unfold finiteCartierClass
  exact supportedFiniteCartierMap_expansion l Y hY c r k n a L _

end AlgebraicGeometry.ProEtale.DiagonalTrace
