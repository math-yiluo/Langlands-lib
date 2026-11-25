/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import WeilConjectures.Mathlib.LinearAlgebra.Trace

/-!
# Alternating sums of traces along a long exact sequence

Let `⋯ → Aₙ → Bₙ → Cₙ → Aₙ₋₁ → Bₙ₋₁ → ⋯` be a long exact sequence of finite-dimensional vector
spaces over a field `K`, indexed by `n : ℤ` and zero for all but finitely many `n`, with
endomorphisms `aₙ`, `bₙ`, `cₙ` commuting with the maps. Then
`∑ₙ (-1)ⁿ (tr bₙ - tr aₙ - tr cₙ) = 0`
(`LinearMap.finsum_negOnePow_smul_trace_sub_trace_sub_trace_eq_zero`). This is the linear algebra
behind the additivity of the categorical trace along distinguished triangles over a field
(blueprint `proposition-properties-trace`, items (2) and (4)).

The proof splits each term along the kernels and images: with `xₙ = tr(aₙ | im fₙ)`,
`yₙ = tr(bₙ | im gₙ)` and `zₙ = tr(cₙ₊₁ | im δₙ₊₁)` one has `tr aₙ = zₙ + xₙ`,
`tr bₙ = xₙ + yₙ` and `tr cₙ = yₙ + zₙ₋₁`, and the alternating sum telescopes.
-/

@[expose] public section

namespace LinearMap

section Additivity

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The trace of an endomorphism of a submodule is independent of the proof that the submodule is
invariant, and is unchanged when the submodule is replaced by an equal one. -/
theorem trace_restrict_congr (φ : V →ₗ[K] V) {p q : Submodule K V} (hpq : p = q)
    (hp : ∀ x ∈ p, φ x ∈ p) (hq : ∀ x ∈ q, φ x ∈ q) :
    trace K p (φ.restrict hp) = trace K q (φ.restrict hq) := by
  subst hpq
  rfl

/-- **Additivity of the trace along an invariant subspace.** If `p` is invariant under `φ`, then
the trace of `φ` is the sum of the traces of its restriction to `p` and of the induced map on
`V ⧸ p`. -/
theorem trace_eq_trace_restrict_add_trace_mapQ [FiniteDimensional K V] (φ : V →ₗ[K] V)
    (p : Submodule K V)
    (hp : ∀ x ∈ p, φ x ∈ p) :
    trace K V φ = trace K p (φ.restrict hp) + trace K (V ⧸ p) (p.mapQ p φ hp) := by
  obtain ⟨q, hq⟩ := p.exists_isCompl
  have h₁ : p.projectionOnto q hq ∘ₗ φ ∘ₗ p.subtype = φ.restrict hp := by
    ext x
    simp [Submodule.projectionOnto_apply_of_mem_left hq (hp x x.2)]
  have h₂ : (Submodule.quotientEquivOfIsCompl p q hq).conj (p.mapQ p φ hp) =
      q.projectionOnto p hq.symm ∘ₗ φ ∘ₗ q.subtype := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [← trace_conj' (p.mapQ p φ hp) (Submodule.quotientEquivOfIsCompl p q hq), h₂, ← h₁,
    ← trace_comp_comm' (p.projectionOnto q hq) (φ ∘ₗ p.subtype),
    ← trace_comp_comm' (q.projectionOnto p hq.symm) (φ ∘ₗ q.subtype), ← map_add, comp_assoc,
    comp_assoc, ← comp_add]
  nth_rw 1 [← comp_id φ, ← Submodule.projection_add_projection_eq_id hq]
  rfl

/-- If `ψ ∘ h = h ∘ φ`, then `φ` preserves the kernel of `h`. -/
theorem map_mem_ker_of_comp_eq {φ : V →ₗ[K] V} {ψ : W →ₗ[K] W} {h : V →ₗ[K] W}
    (hc : ψ ∘ₗ h = h ∘ₗ φ) : ∀ x ∈ ker h, φ x ∈ ker h := by
  intro x hx
  rw [mem_ker] at hx ⊢
  rw [← comp_apply, ← hc, comp_apply, hx, map_zero]

/-- If `ψ ∘ h = h ∘ φ`, then `ψ` preserves the range of `h`. -/
theorem map_mem_range_of_comp_eq {φ : V →ₗ[K] V} {ψ : W →ₗ[K] W} {h : V →ₗ[K] W}
    (hc : ψ ∘ₗ h = h ∘ₗ φ) : ∀ y ∈ range h, ψ y ∈ range h := by
  rintro _ ⟨x, rfl⟩
  exact ⟨φ x, by rw [← comp_apply, ← hc, comp_apply]⟩

/-- If `ψ ∘ h = h ∘ φ`, then the trace of `φ` is the sum of the trace of `φ` restricted to the
kernel of `h` and the trace of `ψ` restricted to the range of `h`. -/
theorem trace_eq_trace_restrict_ker_add_trace_restrict_range [FiniteDimensional K V]
    [FiniteDimensional K W] {φ : V →ₗ[K] V} {ψ : W →ₗ[K] W} {h : V →ₗ[K] W} (hc : ψ ∘ₗ h = h ∘ₗ φ) :
    trace K V φ = trace K (ker h) (φ.restrict (map_mem_ker_of_comp_eq hc)) +
      trace K (range h) (ψ.restrict (map_mem_range_of_comp_eq hc)) := by
  rw [trace_eq_trace_restrict_add_trace_mapQ φ _ (map_mem_ker_of_comp_eq hc),
    ← trace_conj' _ h.quotKerEquivRange]
  congr 2
  ext ⟨_, x, rfl⟩
  simpa [LinearEquiv.conj_apply] using (LinearMap.congr_fun hc x).symm

end Additivity

/-- **Telescoping of alternating sums.** If `w n` and `w (n - 1)` vanish for `n ∉ s`, then
`∑ n ∈ s, (-1)ⁿ • (w n + w (n - 1)) = 0`. -/
theorem _root_.Finset.sum_negOnePow_smul_add_sub_one_eq_zero {M : Type*} [AddCommGroup M]
    (w : ℤ → M) (s : Finset ℤ) (hw : ∀ n ∉ s, w n = 0) (hw' : ∀ n ∉ s, w (n - 1) = 0) :
    ∑ n ∈ s, (n.negOnePow : ℤ) • (w n + w (n - 1)) = 0 := by
  have hshift : ∑ᶠ n : ℤ, (n.negOnePow : ℤ) • w (n - 1) = -∑ᶠ n : ℤ, (n.negOnePow : ℤ) • w n := by
    rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ))]
    simp [Int.negOnePow_succ, finsum_neg_distrib]
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib,
    ← finsum_eq_sum_of_support_subset (fun n ↦ (n.negOnePow : ℤ) • w n)
      (fun n hn ↦ by_contra fun h ↦ hn (by simp [hw n h])),
    ← finsum_eq_sum_of_support_subset (fun n ↦ (n.negOnePow : ℤ) • w (n - 1))
      (fun n hn ↦ by_contra fun h ↦ hn (by simp [hw' n h])), hshift, add_neg_cancel]

variable {K : Type*} [Field K] (A B C : ℤ → Type*) [∀ n, AddCommGroup (A n)]
  [∀ n, Module K (A n)] [∀ n, FiniteDimensional K (A n)] [∀ n, AddCommGroup (B n)]
  [∀ n, Module K (B n)] [∀ n, FiniteDimensional K (B n)] [∀ n, AddCommGroup (C n)]
  [∀ n, Module K (C n)] [∀ n, FiniteDimensional K (C n)]

/-- **Alternating sums of traces along a long exact sequence.** Let
`f n : A n → B n`, `g n : B n → C n` and `δ n : C n → A (n - 1)` form an exact sequence
`⋯ → A n → B n → C n → A (n - 1) → ⋯` of finite-dimensional vector spaces, zero outside a finite
set `s` of indices, and let `a n`, `b n`, `c n` be endomorphisms compatible with the maps. Then
`∑ n ∈ s, (-1)ⁿ • (tr (b n) - tr (a n) - tr (c n)) = 0`. -/
theorem sum_negOnePow_smul_trace_sub_trace_sub_trace_eq_zero
    (f : ∀ n, A n →ₗ[K] B n) (g : ∀ n, B n →ₗ[K] C n) (δ : ∀ n, C n →ₗ[K] A (n - 1))
    (hfg : ∀ n, Function.Exact (f n) (g n)) (hgδ : ∀ n, Function.Exact (g n) (δ n))
    (hδf : ∀ n, Function.Exact (δ n) (f (n - 1)))
    (a : ∀ n, A n →ₗ[K] A n) (b : ∀ n, B n →ₗ[K] B n) (c : ∀ n, C n →ₗ[K] C n)
    (ha : ∀ n, b n ∘ₗ f n = f n ∘ₗ a n) (hb : ∀ n, c n ∘ₗ g n = g n ∘ₗ b n)
    (hc : ∀ n, a (n - 1) ∘ₗ δ n = δ n ∘ₗ c n) (s : Finset ℤ)
    (hA : ∀ n ∉ s, Subsingleton (A n))
    (hC : ∀ n ∉ s, Subsingleton (C n)) :
    ∑ n ∈ s, (n.negOnePow : ℤ) •
      (trace K (B n) (b n) - trace K (A n) (a n) - trace K (C n) (c n)) = 0 := by
  set w : ℤ → K := fun m ↦ trace K _ ((a m).restrict (map_mem_ker_of_comp_eq (ha m)))
  set x : ℤ → K := fun n ↦ trace K _ ((b n).restrict (map_mem_ker_of_comp_eq (hb n)))
  set y : ℤ → K := fun n ↦ trace K _ ((c n).restrict (map_mem_ker_of_comp_eq (hc n))) with hy
  have htra (n : ℤ) : trace K (A n) (a n) = w n + x n := by
    rw [trace_eq_trace_restrict_ker_add_trace_restrict_range (ha n),
      trace_restrict_congr _ (hfg n).linearMap_ker_eq.symm _ (map_mem_ker_of_comp_eq (hb n))]
  have htrb (n : ℤ) : trace K (B n) (b n) = x n + y n := by
    rw [trace_eq_trace_restrict_ker_add_trace_restrict_range (hb n),
      trace_restrict_congr _ (hgδ n).linearMap_ker_eq.symm _ (map_mem_ker_of_comp_eq (hc n))]
  have htrc (n : ℤ) : trace K (C n) (c n) = y n + w (n - 1) := by
    rw [trace_eq_trace_restrict_ker_add_trace_restrict_range (hc n),
      trace_restrict_congr _ (hδf n).linearMap_ker_eq.symm _ (map_mem_ker_of_comp_eq (ha (n - 1)))]
  have key (n : ℤ) : trace K (B n) (b n) - trace K (A n) (a n) - trace K (C n) (c n) =
      -(w n + w (n - 1)) := by
    rw [htra, htrb, htrc]
    ring
  simp_rw [key, smul_neg, Finset.sum_neg_distrib, neg_eq_zero]
  refine Finset.sum_negOnePow_smul_add_sub_one_eq_zero w s (fun n hn ↦ ?_) (fun n hn ↦ ?_)
  · have := hA n hn
    exact trace_eq_zero_of_subsingleton _
  · have := hC n hn
    have h := htrc n
    rw [trace_eq_zero_of_subsingleton, hy] at h
    beta_reduce at h
    rw [trace_eq_zero_of_subsingleton, zero_add] at h
    exact h.symm

end LinearMap
