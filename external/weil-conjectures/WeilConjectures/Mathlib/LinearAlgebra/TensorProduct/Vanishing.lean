/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG

/-!
# Vanishing of a sum of pure tensors through finitely many linear relations

If `∑ₖ mₖ ⊗ gₖ = 0` in `M ⊗ N`, this vanishing is witnessed by finitely many elements of `M`
and finitely many `R`-linear relations between them
(`TensorProduct.exists_relations_of_sum_tmul_eq_zero`): there are `y : Fin s → M`, a matrix
`a` with `mₖ = ∑ⱼ aₖⱼ yⱼ`, and a matrix `e` with `∑ⱼ eₗⱼ yⱼ = 0`, such that every solution `b`
of the relations `e` satisfies `∑ₖ (∑ⱼ aₖⱼ bⱼ) gₖ = 0`.

This is the form in which the vanishing transports along maps out of `M` that preserve the
relations `e` locally, as in the proof that pullback of sheaves preserves flatness.
-/

@[expose] public section

open Function Submodule

namespace TensorProduct

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]

/-- **Vanishing of a sum of pure tensors through finitely many relations.** If
`∑ₖ mₖ ⊗ gₖ = 0` in `M ⊗ N`, there are elements `y : Fin s → M`, a matrix `a` with
`mₖ = ∑ⱼ aₖⱼ yⱼ` and a matrix `e` of relations `∑ⱼ eₗⱼ yⱼ = 0`, such that every
`b : Fin s → R` with `∑ⱼ eₗⱼ bⱼ = 0` for all `l` satisfies `∑ₖ (∑ⱼ aₖⱼ bⱼ) • gₖ = 0`. -/
theorem exists_relations_of_sum_tmul_eq_zero {n : ℕ} (m : Fin n → M) (g : Fin n → N)
    (h : ∑ k, m k ⊗ₜ[R] g k = 0) :
    ∃ (s q : ℕ) (y : Fin s → M) (a : Fin n → Fin s → R) (e : Fin q → Fin s → R),
      (∀ k, m k = ∑ j, a k j • y j) ∧ (∀ l, ∑ j, e l j • y j = 0) ∧
        ∀ b : Fin s → R, (∀ l, ∑ j, e l j * b j = 0) → ∑ k, (∑ j, a k j * b j) • g k = 0 := by
  classical
  -- the vanishing already happens in `Q ⊗ M` for a finitely generated `Q ⊆ N` containing `g`
  let P : Submodule R N := span R (Set.range g)
  have hP : P.FG := fg_span (Set.finite_range g)
  let t : P ⊗[R] M := ∑ k, (⟨g k, subset_span ⟨k, rfl⟩⟩ : P) ⊗ₜ m k
  have ht : LinearMap.rTensor M P.subtype t = 0 := by
    simp only [t, map_sum, LinearMap.rTensor_tmul, Submodule.subtype_apply]
    simpa using congrArg (TensorProduct.comm R M N) h
  obtain ⟨Q, hPQ, ⟨S, hS⟩, hQ⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hP ht
  -- a spanning family of `Q`: the `gₖ` followed by the generators of `Q`
  let p := S.card
  let gen : Fin p → Q := fun l ↦ ⟨(S.equivFin.symm l : N), by
    rw [← hS]; exact subset_span (S.equivFin.symm l).2⟩
  let gg : Fin n ⊕ Fin p → Q := Sum.elim (fun k ↦ inclusion hPQ ⟨g k, subset_span ⟨k, rfl⟩⟩) gen
  let mm : Fin n ⊕ Fin p → M := Sum.elim m 0
  have hspan : span R (Set.range gg) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ span R (S : Set N) := by rwa [hS]
    have key : span R (S : Set N) ≤ (span R (Set.range gg)).map Q.subtype := by
      rw [span_le]
      intro z hz
      refine ⟨⟨z, by rw [← hS]; exact subset_span hz⟩, subset_span
        ⟨Sum.inr (S.equivFin ⟨z, hz⟩), ?_⟩, rfl⟩
      simp [gg, gen]
    obtain ⟨w, hw, hwx⟩ := key hx'
    have : w = ⟨x, hx⟩ := Subtype.ext hwx
    rwa [← this]
  have hsum : ∑ i, gg i ⊗ₜ[R] mm i = (0 : Q ⊗[R] M) := by
    rw [Fintype.sum_sum_type]
    simp only [gg, mm, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, tmul_zero,
      Finset.sum_const_zero, add_zero]
    rw [← hQ]
    simp [t, map_sum]
  obtain ⟨s, c, y, hmy, hcg⟩ := vanishesTrivially_of_sum_tmul_eq_zero R hspan hsum
  refine ⟨s, p, y, fun k j ↦ c (Sum.inl k) j, fun l j ↦ c (Sum.inr l) j,
    fun k ↦ hmy (Sum.inl k), fun l ↦ by simpa [mm] using (hmy (Sum.inr l)).symm, ?_⟩
  intro b hb
  -- `∑ₖ (∑ⱼ aₖⱼ bⱼ) gₖ = - ∑ₗ (∑ⱼ eₗⱼ bⱼ) genₗ = 0` inside `Q`
  have hQeq : ∑ k, (∑ j, c (Sum.inl k) j * b j) • gg (Sum.inl k) =
      -∑ l, (∑ j, c (Sum.inr l) j * b j) • gg (Sum.inr l) := by
    rw [eq_neg_iff_add_eq_zero]
    have h0 : ∑ j, b j • ∑ i, c i j • gg i = 0 := by simp [hcg]
    rw [← h0]
    simp only [Fintype.sum_sum_type, smul_add, Finset.smul_sum, smul_smul,
      Finset.sum_add_distrib, Finset.sum_smul]
    rw [Finset.sum_comm (f := fun j k ↦ (b j * c (Sum.inl k) j) • gg (Sum.inl k)),
      Finset.sum_comm (f := fun j l ↦ (b j * c (Sum.inr l) j) • gg (Sum.inr l))]
    simp only [mul_comm]
  have hQ0 : ∑ k, (∑ j, c (Sum.inl k) j * b j) • gg (Sum.inl k) = 0 := by
    rw [hQeq]; simp [hb]
  have := congrArg (fun x : Q ↦ (x : N)) hQ0
  simpa [gg] using this

end TensorProduct
