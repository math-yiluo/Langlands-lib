/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.LinearAlgebra.TraceLongExactSequence

/-!
# Alternating sums of traces along a cohomological long exact sequence

The additivity of alternating sums of traces of
`WeilConjectures.LinearAlgebra.TraceLongExactSequence`, for a cohomological long exact sequence
`⋯ → Aₙ → Bₙ → Cₙ → Aₙ₊₁ → ⋯` of finite-dimensional vector spaces with compatible endomorphisms
`aₙ`, `bₙ`, `cₙ`, zero outside a finite set of indices, in the form
`∑ᶠ (-1)ⁿ tr bₙ = ∑ᶠ (-1)ⁿ tr aₙ + ∑ᶠ (-1)ⁿ tr cₙ`.

## Main statements

- `LinearMap.finsum_negOnePow_smul_trace_eq_sum_neg`: an alternating sum of traces as a finite
  sum over the negated indices.
- `LinearMap.finsum_negOnePow_smul_trace_eq_add_of_exact`: additivity of alternating sums of
  traces along a bounded cohomological long exact sequence.
-/

@[expose] public section

open scoped Pointwise

namespace LinearMap

variable {K : Type*} [Field K]

/-- An alternating sum of traces over `ℤ`, supported on a finite set `s`, is the corresponding
finite sum over `-s` with the indices negated. -/
theorem finsum_negOnePow_smul_trace_eq_sum_neg (D : ℤ → Type*) [∀ n, AddCommGroup (D n)]
    [∀ n, Module K (D n)] [∀ n, FiniteDimensional K (D n)] (d : ∀ n, D n →ₗ[K] D n)
    (s : Finset ℤ) (hD : ∀ n ∉ s, Subsingleton (D n)) :
    ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • trace K (D n) (d n) =
      ∑ n ∈ -s, (n.negOnePow : ℤ) • trace K (D (-n)) (d (-n)) := by
  rw [← finsum_comp_equiv (Equiv.neg ℤ)]
  refine (finsum_eq_sum_of_support_subset _ fun n hn ↦ ?_).trans
    (Finset.sum_congr rfl fun n _ ↦ by rw [Equiv.neg_apply, Int.negOnePow_neg])
  rw [Finset.mem_coe, Finset.mem_neg']
  by_contra h
  have := hD _ h
  refine hn ?_
  beta_reduce
  rw [Equiv.neg_apply, trace_eq_zero_of_subsingleton, smul_zero]

variable (A B C : ℤ → Type*) [∀ n, AddCommGroup (A n)]
  [∀ n, Module K (A n)] [∀ n, FiniteDimensional K (A n)] [∀ n, AddCommGroup (B n)]
  [∀ n, Module K (B n)] [∀ n, FiniteDimensional K (B n)] [∀ n, AddCommGroup (C n)]
  [∀ n, Module K (C n)] [∀ n, FiniteDimensional K (C n)]

/-- **Alternating sums of traces along a cohomological long exact sequence.** Let
`f n : A n → B n`, `g n : B n → C n` and `δ n n' : C n → A n'` (for `n + 1 = n'`) form an exact
sequence `⋯ → A n → B n → C n → A (n + 1) → ⋯` of finite-dimensional vector spaces, zero outside a
finite set of indices, and let `a n`, `b n`, `c n` be endomorphisms compatible with the maps. Then
`∑ₙ (-1)ⁿ tr (b n) = ∑ₙ (-1)ⁿ tr (a n) + ∑ₙ (-1)ⁿ tr (c n)`. -/
theorem finsum_negOnePow_smul_trace_eq_add_of_exact
    (f : ∀ n, A n →ₗ[K] B n) (g : ∀ n, B n →ₗ[K] C n)
    (δ : ∀ n n', n + 1 = n' → C n →ₗ[K] A n')
    (hfg : ∀ n, Function.Exact (f n) (g n))
    (hgδ : ∀ n n' (h : n + 1 = n'), Function.Exact (g n) (δ n n' h))
    (hδf : ∀ n n' (h : n + 1 = n'), Function.Exact (δ n n' h) (f n'))
    (a : ∀ n, A n →ₗ[K] A n) (b : ∀ n, B n →ₗ[K] B n) (c : ∀ n, C n →ₗ[K] C n)
    (ha : ∀ n, b n ∘ₗ f n = f n ∘ₗ a n) (hb : ∀ n, c n ∘ₗ g n = g n ∘ₗ b n)
    (hc : ∀ n n' (h : n + 1 = n'), a n' ∘ₗ δ n n' h = δ n n' h ∘ₗ c n) (s : Finset ℤ)
    (hA : ∀ n ∉ s, Subsingleton (A n)) (hB : ∀ n ∉ s, Subsingleton (B n))
    (hC : ∀ n ∉ s, Subsingleton (C n)) :
    ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • trace K (B n) (b n) =
      ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • trace K (A n) (a n) +
        ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • trace K (C n) (c n) := by
  have key := sum_negOnePow_smul_trace_sub_trace_sub_trace_eq_zero (K := K)
    (fun n ↦ A (-n)) (fun n ↦ B (-n)) (fun n ↦ C (-n)) (fun n ↦ f (-n)) (fun n ↦ g (-n))
    (fun n ↦ δ (-n) (-(n - 1)) (by omega)) (fun n ↦ hfg (-n)) (fun n ↦ hgδ _ _ _)
    (fun n ↦ hδf _ _ _) (fun n ↦ a (-n)) (fun n ↦ b (-n)) (fun n ↦ c (-n)) (fun n ↦ ha (-n))
    (fun n ↦ hb (-n)) (fun n ↦ hc _ _ _) (-s)
    (fun n hn ↦ hA _ (by rwa [Finset.mem_neg'] at hn))
    (fun n hn ↦ hC _ (by rwa [Finset.mem_neg'] at hn))
  rw [finsum_negOnePow_smul_trace_eq_sum_neg A a s hA,
    finsum_negOnePow_smul_trace_eq_sum_neg B b s hB,
    finsum_negOnePow_smul_trace_eq_sum_neg C c s hC, ← Finset.sum_add_distrib, ← sub_eq_zero,
    ← Finset.sum_sub_distrib, ← key]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [smul_sub, smul_sub, sub_sub]


end LinearMap
