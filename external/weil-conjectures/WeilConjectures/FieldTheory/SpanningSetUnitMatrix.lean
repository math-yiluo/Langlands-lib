/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Basis

/-! Extracting an invertible column matrix from a spanning set. -/
@[expose] public section
universe u
namespace Matrix
/-- A spanning set in F^n contains the columns of a unit matrix.
Source: Stacks Project, Tag 03R7, extraction of an invariant basis.
(blueprint: lem-sc-spanning-set-unit-matrix) -/
theorem exists_unit_matrix_columns_mem (F : Type u) [Field F] (n : ℕ)
    (s : Set (Fin n → F)) (hs : Submodule.span F s = ⊤) :
    ∃ t : GeneralLinearGroup (Fin n) F, ∀ j, (fun i ↦ t.val i j) ∈ s := by
  classical
  have hdim : Module.finrank F (Submodule.span F s) = n := by
    rw [hs, finrank_top]
    simp
  have hex := Submodule.exists_fun_fin_finrank_span_eq F s
  rw [hdim] at hex
  obtain ⟨f, hf, hspan, hli⟩ := hex
  let B := Module.Basis.mk hli (by rw [hspan, hs])
  let E := Pi.basisFun F (Fin n)
  let t : GeneralLinearGroup (Fin n) F :=
    ⟨E.toMatrix B, B.toMatrix E,
      E.toMatrix_mul_toMatrix_flip B, B.toMatrix_mul_toMatrix_flip E⟩
  refine ⟨t, ?_⟩
  intro j
  convert hf j using 1
  ext i
  simp [t, E, Module.Basis.toMatrix_apply, B]
end Matrix
