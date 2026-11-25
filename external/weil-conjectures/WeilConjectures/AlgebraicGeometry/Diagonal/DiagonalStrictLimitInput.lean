/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalStrictLimitSpecification

/-! # Recover the strict witnesses from the diagonal cycle system -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Lean Meta Elab Tactic
namespace AlgebraicGeometry.ProEtale

/-- Recover the strict witnesses and their finite heterogeneous equations.
Source: normalizedBoundarySystem_iff_target
(blueprint: lem-sfb-diagonal-strict-limit-input).
Proof: apply the existing equivalence; the named finite input predicate is its
finite endpoint and class equation, by definitional equality. -/
theorem diagonal_strict_limit_input (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hsystem : DiagonalCycleSystemSpec ℓ Y hY D) :
    DiagonalStrictInputSpec ℓ Y hY D := by
  -- Instantiate the system equivalence with its stored normalization functions.
  run_tac withMainContext do
    let named := (← getMainTarget).consumeMData
    let some source ← unfoldDefinition? named |
      throwError "Cannot unfold the strict input specification"
    unless source.isAppOf ``DiagonalStrictDataSpec do
      throwError "Unexpected strict limit specification"
    let some hsys := (← getLCtx).findFromUserName? `hsystem |
      throwError "Missing system hypothesis"
    let some sysType ← unfoldDefinition? (← inferType hsys.toExpr) |
      throwError "Cannot unfold the cycle system"
    let iff ← lambdaTelescope sysType.getAppArgs.back! fun _ body => do
      let some target ← unfoldDefinition? body.getAppArgs.back! |
        throwError "Cannot unfold the boundary target"
      mkAppOptM ``normalizedBoundarySystem_iff_target (target.getAppArgs.pop.map some)
    let system ← mkAppM ``Iff.mpr #[iff, hsys.toExpr]
    (← getMainGoal).assign system
    replaceMainGoal []

end AlgebraicGeometry.ProEtale
