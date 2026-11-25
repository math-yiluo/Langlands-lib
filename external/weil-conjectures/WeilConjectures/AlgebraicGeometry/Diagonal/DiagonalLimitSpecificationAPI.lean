/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitAssembly
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitNormalizations

/-! # Named data for the diagonal limit specification

These definitions spell out the existing specification with shared endpoint and
normalization functions. No coefficient object or boundary is changed.
(blueprint: def-sfb-diagonal-limit-specification-api).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The original assertion with its repeated functions named. Every constituent
is the actual coefficient object, class or equation of DiagonalCompletedLimitSpec. -/
def DiagonalTypedLimitSpec (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y))) :
    Prop :=
  DiagonalLimitDataSpec ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)) D
    (diagonalIntegralSource Y) (diagonalComparisonUnits Y) (diagonalIntegralBoundary Y)
    (diagonalCompletedRestriction ℓ (diagonalSurface Y))
    (diagonalCompletedSource ℓ Y) (Scheme.purTwistZlModule (diagonalSurface Y) ℓ)
    (diagonalLimitRoots ℓ Y) (diagonalLimitFiniteNormalization ℓ Y hY D)
    (diagonalLimitSourceNorm ℓ Y D) (diagonalLimitTargetNorm ℓ Y)

/-- The named-data assertion gives the original limit specification verbatim.
Source: the definition of DiagonalCompletedLimitSpec
(blueprint: def-sfb-diagonal-limit-specification-api).
Proof: unfold only the named functions; each is the original function body. -/
theorem diagonalLimitSpec_of_typed (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (h : DiagonalTypedLimitSpec ℓ Y hY D) : DiagonalCompletedLimitSpec ℓ Y hY D := by
  exact h

end AlgebraicGeometry.ProEtale
