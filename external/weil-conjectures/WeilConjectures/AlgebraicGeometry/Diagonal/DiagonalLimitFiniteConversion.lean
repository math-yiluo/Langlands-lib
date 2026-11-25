/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitInputFinite
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalCompletedDataAssembly

/-! # Homogeneous finite normalization equations

The predicate is the finite part of the given normalized strict system.
(blueprint: lem-sfb-diagonal-limit-finite-conversion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Lean Meta Elab Tactic
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CategoryTheory.Abelian.Ext
  diagonalLimitFiniteSource diagonalLimitFiniteTarget diagonalLimitFiniteClass
  diagonalLimitFiniteSourceNorm diagonalLimitFiniteTargetNorm diagonalLimitRoots

/-- Convert the supplied heterogeneous finite equations to the finite normalization.
Source: the finite normalization definitions
(blueprint: lem-sfb-diagonal-limit-finite-conversion).
Proof: retain every pair of endpoint isomorphisms and the two normalizations, then
use eq_of_heq for the homogeneous class equation. The named input predicate and
normalization use exactly the same endpoint and class functions. -/
theorem diagonalLimitFiniteNormalization_of_input (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (H : DiagonalSystems ℓ (diagonalSurface Y)) (roots : diagonalLimitRoots ℓ Y H)
    (c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2)
    (h : diagonalLimitInputFinite ℓ Y hY D H roots c) :
    diagonalLimitFiniteNormalization ℓ Y hY D H roots c := by
  unfold diagonalLimitFiniteNormalization
  run_tac withMainContext do
    let target := (← getMainTarget).consumeMData
    let proof ← mkAppOptM ``diagonalFiniteCycleNormalization_of_heq
      (target.getAppArgs.map some)
    replaceMainGoal (← (← getMainGoal).apply proof)
  exact h

end AlgebraicGeometry.ProEtale
