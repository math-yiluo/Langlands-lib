/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Expanding tensors along a linearly independent family

Over a field `k`, finitely many tensors `t a ∈ A a ⊗[k] K` can be written simultaneously as
`t a = ∑ q, F a q ⊗ₜ β q` for one linearly independent family `β` of `K`: take for `β` a basis of
the span of the right factors of chosen expansions of the `t a`.

## Main statements

- `TensorProduct.exists_linearIndependent_forall_eq_sum_tmul`: the simultaneous expansion.
-/

@[expose] public section

open TensorProduct

namespace TensorProduct

variable {k K : Type*} [Field k] [AddCommGroup K] [Module k K]

/-- **Simultaneous expansion along a linearly independent family.** Over a field `k`, finitely
many tensors `t a ∈ A a ⊗[k] K` can be written as `t a = ∑ q, F a q ⊗ₜ β q` for a single
linearly independent family `β : Fin N → K`. -/
theorem exists_linearIndependent_forall_eq_sum_tmul {ι : Type*} [Finite ι] {A : ι → Type*}
    [∀ a, AddCommGroup (A a)] [∀ a, Module k (A a)] (t : ∀ a, A a ⊗[k] K) :
    ∃ (N : ℕ) (β : Fin N → K), LinearIndependent k β ∧
      ∀ a, ∃ F : Fin N → A a, t a = ∑ q, F q ⊗ₜ β q := by
  classical
  choose n m r hr using fun a ↦ exists_sum_tmul_eq (t a)
  set S : Set K := ⋃ a, Set.range (r a)
  have hS : S.Finite := Set.finite_iUnion fun a ↦ Set.finite_range _
  set V := Submodule.span k S
  have : FiniteDimensional k V := FiniteDimensional.span_of_finite k hS
  let b := Module.finBasis k V
  refine ⟨Module.finrank k V, fun q ↦ b q, b.linearIndependent.map' V.subtype V.ker_subtype,
    fun a ↦ ?_⟩
  have hmem (j : Fin (n a)) : r a j ∈ V :=
    Submodule.subset_span (Set.mem_iUnion.mpr ⟨a, j, rfl⟩)
  refine ⟨fun q ↦ ∑ j, b.repr ⟨r a j, hmem j⟩ q • m a j, ?_⟩
  rw [hr a]
  simp_rw [sum_tmul, smul_tmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← tmul_sum]
  congr 1
  have h := congrArg Subtype.val (b.sum_repr ⟨r a j, hmem j⟩)
  rw [Submodule.coe_sum] at h
  exact h.symm

end TensorProduct
