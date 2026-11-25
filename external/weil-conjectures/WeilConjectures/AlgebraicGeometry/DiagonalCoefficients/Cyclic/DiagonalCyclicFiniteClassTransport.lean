/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCoefficientInstances
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicFiniteClassTransportEquation
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicTransportEquation

/-! # Literal proposition wrapper for the cyclic transport equation

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: lem-diagonal-cyclic-finite-class-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 4000] cyclicCoefficientHasExt

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  geoCartierConstant geoCartierLine cartierRootsIso cartierEtaleKummerUnit
  cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary Functor.mapDerivedCategory shiftFunctor

attribute [local irreducible] cyclicLine cyclicLineMap derivedScalars
  diagonalSingleLimitComparison diagonalShiftedSingleLimitComparison

attribute [local irreducible] CyclicCartierFrame.reduce

attribute [local semireducible] finiteCyclicTransportEquation cyclicTransportEquation
  DiagonalTrace.finiteCartierClass

attribute [local semireducible] cyclicRestrictedFrameClass

/-- The named canonical finite class is the original exact-functor image.
Source: definition of the finite Cartier class
(blueprint: lem-diagonal-cyclic-finite-class-transport).
Proof: unfold both literal equation predicates, the canonical finite class and
its generic exact-functor image wrapper. The given equality has precisely the
original conclusion. No finite normalization or coefficient comparison is used. -/
theorem finiteCyclicTransport_to_transportEquation
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (family : Family l Y) (n : ℕ) (p : CyclicCartierFrame l Y n)
    (h : finiteCyclicTransportEquation l Y hY family n p) :
    cyclicTransportEquation l Y hY family n p := by
  exact h

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
