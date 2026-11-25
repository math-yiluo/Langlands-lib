/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitNormalizations
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalCompletedDataAssembly

/-! # Finite equations before homogeneous equality conversion

The predicate is the finite part of the given normalized strict system.
(blueprint: def-sfb-diagonal-limit-input-finite).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- The finite endpoint normalizations and heterogeneous class equations supplied
by the normalized boundary system, expressed with named endpoint functions. -/
def diagonalLimitInputFinite (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (H : DiagonalSystems ℓ (diagonalSurface Y)) (roots : diagonalLimitRoots ℓ Y H)
    (c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2) : Prop :=
  diagonalFiniteCycleNormalizationHEq (D.ordinary.E.obj (diagonalIntegralSource Y)) H c
    (diagonalLimitFiniteSource ℓ Y) (diagonalLimitFiniteTarget ℓ Y)
    (diagonalLimitFiniteSourceNorm ℓ Y D)
    (diagonalLimitFiniteTargetNorm ℓ Y hY H roots) (diagonalLimitFiniteClass ℓ Y hY)

end AlgebraicGeometry.ProEtale
