/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierNormalization
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteBoundarySourceAlgebra
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierCoordinateNormalization

/-! # Assembling the finite coordinate equation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap diagonalCompletedRestriction

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
  completedSupportedUnit

/-- The given finite normalization in the shared diagonal module coordinates.
Source: diagonal trace proof (2), finite source projection; diagonal-system proof (4).
(blueprint: lem-sfb-diagonal-trace-finite-cartier-normalized-coordinates).

Proof: unfold the finite normalization at n and take its source and target
coordinates. Retain the source generator and root equations. Unfold the named
normalized Ext expression and typed Cartier class: they are precisely the finite
cycle equation already supplied by the normalization. The cached diagonal Ext
witness changes only the spelling of definitionally equal categorical structures. -/
theorem finiteCartierNormalization_coordinates
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (xi : @Ext (DiagonalSystems l (diagonalSurface Y)) _ _
      (DiagonalTraceLocalizations.ext (ℓ := l) (X := diagonalSurface Y))
      (D.E.obj (diagonalIntegralSource Y)) H 2)
    (hxi : @FiniteCartierNormalization l _ Y hY
      (DiagonalTraceLocalizations.ext (ℓ := l) (X := diagonalSurface Y)) D H roots xi)
    (n : ℕ) : FiniteCartierCoordinateNormalization l Y hY D H roots xi n := by
  unfold FiniteCartierCoordinateNormalization normalizedFiniteExtClass
    finiteCartierCoordinateClass
  unfold FiniteCartierNormalization diagonalFiniteCycleNormalization at hxi
  exact hxi n

end AlgebraicGeometry.ProEtale.DiagonalTrace
