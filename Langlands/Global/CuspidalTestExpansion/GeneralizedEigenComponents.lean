import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Generalized eigencomponents lie in every invariant subspace containing their sum -/

open Polynomial

set_option autoImplicit false

namespace Langlands.Global.GeneralizedEigenComponents

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {B : Type*} (T : B → Module.End ℂ V)

/-- A submodule invariant under one endomorphism is invariant under every polynomial in it. -/
theorem aeval_apply_mem (W : Submodule ℂ V) {S : Module.End ℂ V} (hS : ∀ x ∈ W, S x ∈ W)
    (p : ℂ[X]) {x : V} (hx : x ∈ W) : aeval S p x ∈ W := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact W.add_mem hp hq
  | monomial n a =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine W.smul_mem a ?_
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hS _ ih

theorem aeval_X_sub_C_pow (S : Module.End ℂ V) (α : ℂ) (N : ℕ) :
    aeval S ((X - C α) ^ N) = (S - α • 1) ^ N := by
  rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

/-- Let `W` be a submodule invariant under a commuting family `T`. If a finite sum of generalized
joint eigenvectors with pairwise distinct eigencharacters lies in `W`, so does every summand. -/
theorem mem_of_sum_mem (hT : ∀ a b, Commute (T a) (T b)) {ι : Type*} [DecidableEq ι]
    (χ : ι → B → ℂ) (W : Submodule ℂ V) (hW : ∀ b, ∀ x ∈ W, T b x ∈ W) :
    ∀ (s : Finset ι), (∀ i ∈ s, ∀ j ∈ s, χ i = χ j → i = j) →
      ∀ (c : ι → V), (∀ i ∈ s, ∀ b, ∃ k : ℕ, ((T b - χ i b • 1) ^ k) (c i) = 0) →
        ∑ i ∈ s, c i ∈ W → ∀ i ∈ s, c i ∈ W := by
  intro s
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ m ih =>
  intro hχ c hgen hsum
  by_cases hs : ∃ i ∈ s, ∃ j ∈ s, i ≠ j
  · obtain ⟨i₀, hi₀, i₁, hi₁, hne⟩ := hs
    have hχne : χ i₀ ≠ χ i₁ := fun h => hne (hχ _ hi₀ _ hi₁ h)
    obtain ⟨b, hb⟩ : ∃ b, χ i₀ b ≠ χ i₁ b := Function.ne_iff.mp hχne
    set α := χ i₀ b with hα
    let s₀ := s.filter (fun i => χ i b = α)
    let s₁ := s.filter (fun i => χ i b ≠ α)
    choose! k hk using fun i hi => hgen i hi b
    let N := ∑ i ∈ s, k i
    let P : Module.End ℂ V := (T b - α • 1) ^ N
    have hPW : ∀ x ∈ W, P x ∈ W := by
      intro x hx
      show ((T b - α • 1) ^ N) x ∈ W
      rw [← aeval_X_sub_C_pow]
      exact aeval_apply_mem W (hW b) _ hx
    have hkN : ∀ i ∈ s, k i ≤ N := fun i hi =>
      Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) hi
    have hP0 : ∀ i ∈ s₀, P (c i) = 0 := by
      intro i hi
      obtain ⟨his, hiα⟩ := Finset.mem_filter.mp hi
      have hkill := hk i his
      rw [hiα] at hkill
      change ((T b - α • 1) ^ N) (c i) = 0
      rw [← Nat.sub_add_cancel (hkN i his), pow_add, Module.End.mul_apply, hkill, map_zero]
    have hsplit : ∑ i ∈ s, c i = ∑ i ∈ s₀, c i + ∑ i ∈ s₁, c i :=
      (Finset.sum_filter_add_sum_filter_not s (fun i => χ i b = α) c).symm
    have hsum₁ : ∑ i ∈ s₁, P (c i) ∈ W := by
      have h := hPW _ hsum
      rw [hsplit, map_add, map_sum, map_sum, Finset.sum_eq_zero hP0, zero_add] at h
      exact h
    have hcomm (b' : B) (β : ℂ) (j : ℕ) : Commute P ((T b' - β • 1) ^ j) := by
      apply Commute.pow_pow
      exact ((hT b b').sub_right (Commute.smul_right (Commute.one_right _) β)).sub_left
        ((Commute.smul_left (Commute.one_left _) α).sub_right
          (Commute.smul_right (Commute.one_right _) β))
    have hgen₁ : ∀ i ∈ s₁, ∀ b', ∃ j : ℕ, ((T b' - χ i b' • 1) ^ j) (P (c i)) = 0 := by
      intro i hi b'
      obtain ⟨j, hj⟩ := hgen i (Finset.mem_filter.mp hi).1 b'
      refine ⟨j, ?_⟩
      rw [← Module.End.mul_apply, ← (hcomm b' (χ i b') j).eq, Module.End.mul_apply, hj, map_zero]
    have hcard₁ : s₁.card < m := by
      rw [← hn]
      apply Finset.card_lt_card
      refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have := Finset.mem_filter.mp (h hi₀)
      exact this.2 rfl
    have hχ₁ : ∀ i ∈ s₁, ∀ j ∈ s₁, χ i = χ j → i = j := fun i hi j hj =>
      hχ i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
    have hP₁ := ih _ hcard₁ s₁ rfl hχ₁ (fun i => P (c i)) hgen₁ hsum₁
    have hc₁ : ∀ i ∈ s₁, c i ∈ W := by
      intro i hi
      obtain ⟨his, hiα⟩ := Finset.mem_filter.mp hi
      have hcop : IsCoprime ((X - C α) ^ N) ((X - C (χ i b)) ^ k i) := by
        apply IsCoprime.pow
        apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hiα))
      obtain ⟨u, v, huv⟩ := hcop
      have h1 := congrArg (fun p => aeval (T b) p (c i)) huv
      simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
        Module.End.one_apply, aeval_X_sub_C_pow, hk i his, map_zero, add_zero] at h1
      rw [← h1]
      exact aeval_apply_mem W (hW b) u (hP₁ i hi)
    have hsum₀ : ∑ i ∈ s₀, c i ∈ W := by
      have h := W.sub_mem hsum (W.sum_mem hc₁)
      rwa [hsplit, add_sub_cancel_right] at h
    have hcard₀ : s₀.card < m := by
      rw [← hn]
      apply Finset.card_lt_card
      refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have := Finset.mem_filter.mp (h hi₁)
      exact hb this.2.symm
    have hχ₀ : ∀ i ∈ s₀, ∀ j ∈ s₀, χ i = χ j → i = j := fun i hi j hj =>
      hχ i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
    have hc₀ := ih _ hcard₀ s₀ rfl hχ₀ c (fun i hi => hgen i (Finset.mem_filter.mp hi).1) hsum₀
    intro i hi
    by_cases hiα : χ i b = α
    · exact hc₀ i (Finset.mem_filter.mpr ⟨hi, hiα⟩)
    · exact hc₁ i (Finset.mem_filter.mpr ⟨hi, hiα⟩)
  · have hs' : ∀ i ∈ s, ∀ j ∈ s, i = j := fun i hi j hj => by
      by_contra h
      exact hs ⟨i, hi, j, hj, h⟩
    intro i hi
    have h : ∑ j ∈ s, c j = c i :=
      Finset.sum_eq_single_of_mem i hi fun j hj hji => (hji (hs' j hj i hi)).elim
    rwa [h] at hsum

end Langlands.Global.GeneralizedEigenComponents
