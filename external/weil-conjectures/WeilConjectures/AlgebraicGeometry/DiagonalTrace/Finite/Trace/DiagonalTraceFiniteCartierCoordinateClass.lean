/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCoefficientInstances

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierClass
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierSourceObject
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierLineObject
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels

/-! # The canonical finite Cartier arrow -/

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

/-- The canonical finite Cartier class with its scalar endpoints explicitly shared.
Source: diagonal trace proof (2), finite Cartier endpoint.
(blueprint: def-sfb-diagonal-trace-finite-cartier-coordinate-class). -/
@[irreducible] def finiteCartierCoordinateClass
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    (n : ℕ) :
    @Ext (DiagonalMod l (diagonalSurface Y))
      (inferInstanceAs (Category (DiagonalMod l (diagonalSurface Y))))
      (inferInstanceAs (Abelian (DiagonalMod l (diagonalSurface Y))))
      (DiagonalCoefficients.cyclicCoefficientHasExt l (diagonalSurface Y))
      (finiteCartierSourceObject l Y n) (finiteCartierLineObject l Y n) 2 :=
  finiteCartierClass l Y hY n

/-- The typed coordinate class is the original canonical class.
Source: diagonal trace proof (2), finite Cartier endpoint.
(blueprint: lem-sfb-diagonal-trace-finite-cartier-coordinate-class-eq).
Proof: unfold the deterministic typed alias. -/
theorem finiteCartierCoordinateClass_eq
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤))) (n : ℕ) :
    finiteCartierCoordinateClass l Y hY n = finiteCartierClass l Y hY n := by
  unfold finiteCartierCoordinateClass
  rfl

end AlgebraicGeometry.ProEtale.DiagonalTrace
