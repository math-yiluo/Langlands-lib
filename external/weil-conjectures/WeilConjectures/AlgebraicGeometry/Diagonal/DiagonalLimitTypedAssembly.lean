/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitSpecificationAPI
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalCompletedDataAssembly
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalLimitCompletedData
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalStrictLimitData

/-! # Assembly with the named diagonal limit specification -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Lean Meta Elab Tactic
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CategoryTheory.Abelian.Ext
  DiagonalLimitDataSpec diagonalCompleteDataAssertion

/-- Assemble the strict and completed data using their shared named normalizations.
Source: diagonal tower limit, clauses (1) and (3)
(blueprint: lem-sfb-diagonal-limit-typed-assembly).
Proof: recover the normalized strict-system witnesses, retain the same endpoint
identifications, and attach the completed compatibility supplied by the endpoint,
finite-reduction and scalar-restriction argument. The generic assembly theorem
retains these witnesses without any additional choice. -/
theorem diagonal_limit_typed_data (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec ℓ Y hY D) :
  DiagonalTypedLimitSpec ℓ Y hY D := by
  unfold DiagonalTypedLimitSpec
  -- Keep the normalizers and implicit instances exactly as stored in the specification.
  run_tac withMainContext do
    let source := (← getMainTarget).consumeMData
    unless source.isAppOf ``DiagonalLimitDataSpec do
      throwError "Unexpected diagonal limit specification"
    let names : Array Name := #[`ℓ, `Y, `hY, `D, `hsystem]
    let args ← names.mapM fun name => do
      let some decl := (← getLCtx).findFromUserName? name | throwError "Missing {name}"
      pure decl.toExpr
    let strict ← mkAppM ``diagonal_strict_limit_data args
    let proof ← mkAppOptM ``diagonalLimitData_of_strict
      ((source.getAppArgs.map some) ++ #[some strict])
    replaceMainGoal (← (← getMainGoal).apply proof)
  intro H roots a b
  run_tac withMainContext do
    let names : Array Name := #[`ℓ, `k, `p, `hpℓ, `Y, `hY, `D, `hcompletion,
      `H, `roots, `a, `b]
    let args ← names.mapM fun name => do
      let some decl := (← getLCtx).findFromUserName? name | throwError "Missing {name}"
      pure decl.toExpr
    let proof ← mkAppM ``diagonal_limit_completed_data args
    (← getMainGoal).assign proof
    replaceMainGoal []

end AlgebraicGeometry.ProEtale
