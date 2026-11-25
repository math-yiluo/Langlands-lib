/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit

/-! # The positive finite supported Cartier classes with fixed scalar endpoints -/

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

/-- The canonical positive Cartier class after restriction of the finite scalars.
The source and target are inferred from the canonical class itself, so the
categorical structures of the finite functor and the Ext class are shared.
Source: diagonal-system finite normalization, clause (4).
(blueprint: def-sfb-diagonal-trace-finite-cartier-class). -/
@[irreducible]
def finiteCartierClass (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤))) (n : ℕ) :=
  diagonalExactFunctorExtImage (diagonalFiniteToPadic l n (diagonalSurface Y))
        (cartierResidueReducedPro l (Fact.out : l.Prime) (n + 1)
          (diagonalImmersion Y) (diagonalImmersion_cartier Y)
          (diagonalSurface_power_unit l Y hY n))

end AlgebraicGeometry.ProEtale.DiagonalTrace
