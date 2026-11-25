/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitInputFinite

/-! # Named strict-system specifications for the diagonal limit

These are the existing strict witnesses with either form of the finite equation.
(blueprint: def-sfb-diagonal-strict-limit-specification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Strict data before replacing the heterogeneous finite equation by equality. -/
def DiagonalStrictInputSpec (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
 : Prop :=
  DiagonalStrictDataSpec ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)) D
    (diagonalIntegralSource Y) (diagonalComparisonUnits Y) (diagonalIntegralBoundary Y)
    (diagonalLimitRoots ℓ Y) (diagonalLimitInputFinite ℓ Y hY D)

/-- Strict data with the finite Cartier normalization used in the limit assertion. -/
def DiagonalStrictLimitSpec (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
 : Prop :=
  DiagonalStrictDataSpec ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)) D
    (diagonalIntegralSource Y) (diagonalComparisonUnits Y) (diagonalIntegralBoundary Y)
    (diagonalLimitRoots ℓ Y) (diagonalLimitFiniteNormalization ℓ Y hY D)

end AlgebraicGeometry.ProEtale
