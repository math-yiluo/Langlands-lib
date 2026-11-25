/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalStrictLimitSpecification
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalStrictLimitInput
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitFiniteConversion

/-! # The strict-system normalization in the diagonal limit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Lean Meta Elab Tactic
namespace AlgebraicGeometry.ProEtale

/-- Convert the recovered strict finite equations into the Cartier normalization.
Source: the diagonal system interface and finite normalization
(blueprint: lem-sfb-diagonal-strict-limit-data).
Proof: preserve the strict witnesses and apply the proved HEq-to-equality conversion
at each finite level. -/
theorem diagonal_strict_limit_data (ℓ : ℕ) [Fact ℓ.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hsystem : DiagonalCycleSystemSpec ℓ Y hY D) :
    DiagonalStrictLimitSpec ℓ Y hY D := by
  run_tac withMainContext do
    let some source ← unfoldDefinition? (← getMainTarget) |
      throwError "Cannot unfold the strict limit specification"
    let names : Array Name := #[`ℓ, `Y, `hY, `D]
    let predicateArgs ← names.mapM fun name => do
      let some decl := (← getLCtx).findFromUserName? name | throwError "Missing {name}"
      pure decl.toExpr
    let inputFinite ← mkAppM ``diagonalLimitInputFinite predicateArgs
    let some hsys := (← getLCtx).findFromUserName? `hsystem |
      throwError "Missing system hypothesis"
    let system ← mkAppM ``diagonal_strict_limit_input (predicateArgs.push hsys.toExpr)
    let args := (source.getAppArgs.map some) ++ #[some inputFinite, some system]
    let proof ← mkAppOptM ``diagonalStrictData_map_finite args
    replaceMainGoal (← (← getMainGoal).apply proof)
  intro H roots c hn
  exact diagonalLimitFiniteNormalization_of_input ℓ Y hY D H roots c hn

end AlgebraicGeometry.ProEtale
