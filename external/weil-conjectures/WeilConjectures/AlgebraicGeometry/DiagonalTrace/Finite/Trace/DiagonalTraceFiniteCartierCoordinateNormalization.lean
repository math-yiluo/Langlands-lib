/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierNormalization
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteBoundarySourceAlgebra
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierCoordinateClass

/-! # Fixed finite Cartier coordinate normalization -/

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

/-- The finite source, root and Ext coordinates at a specified level.
Source: diagonal trace proof (2), finite source projection; diagonal-system proof (4).
(blueprint: def-sfb-diagonal-trace-finite-cartier-coordinate-normalization).
This is the explicit conjunction of the given source and root normalizations and
the canonical finite-cycle equation, with the evaluated Ext expression shared. -/
@[irreducible] def FiniteCartierCoordinateNormalization
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
    (n : ℕ) : Prop :=
    ∃ (sigma : (D.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
        finiteCartierSourceObject l Y n)
      (t : H.obj (op n) ≅ finiteCartierLineObject l Y n),
      DiagonalSourceNormalization l Y D n sigma ∧
      FiniteRootNormalization l Y hY H roots n t ∧
      @normalizedFiniteExtClass (DiagonalMod l (diagonalSurface Y))
        (inferInstanceAs (Category (DiagonalMod l (diagonalSurface Y))))
        (inferInstanceAs (Abelian (DiagonalMod l (diagonalSurface Y))))
        (DiagonalCoefficients.cyclicCoefficientHasExt l (diagonalSurface Y))
        (DiagonalTraceLocalizations.ext (ℓ := l) (X := diagonalSurface Y))
        _ _ xi n _ _ sigma t = finiteCartierCoordinateClass l Y hY n

end AlgebraicGeometry.ProEtale.DiagonalTrace
