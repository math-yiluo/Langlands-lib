/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import WeilConjectures.FieldTheory.FrobeniusClosedBasis.Dedekind
public import WeilConjectures.FieldTheory.FrobeniusClosedBasis.Valuation

/-!
# Frobenius-closed bases of function fields

Let `k` be an algebraically closed field of characteristic `p`, and let `E` be a finite separable
extension of `k⟮x⟯` with `x` transcendental over `k`. Then `E` has a *Frobenius-closed*
`k`-basis: there is a family `w : ι → E` such that `1` together with the `w i ^ p ^ r`
(`i : ι`, `r : ℕ`) form a `k`-basis of `E`.

As a consequence, if `c₀ + ∑ cᵢ wᵢ` is a `p`-th power in `E`, then all `cᵢ` vanish.

Source: F.-V. Kuhlmann, *Additive polynomials and their role in the model theory of valued
fields*, arXiv:1003.5683, Theorem 10, Lemmas 25 and 26.

## Proof

The pole orders at the height-one primes of the integral closures of `k[x]` and `k[x⁻¹]` in `E`
define a filtration of `E` by `k`-subspaces, with `0`-th step `k`, compatible with Frobenius
(`FrobeniusClosedBasis.exists_valuations_of_transcendental`). A Frobenius-closed basis is then
constructed level by level (`FrobeniusClosedBasis.exists_frobeniusClosed_basis_of_filtration`).
-/

@[expose] public section

universe v

open Polynomial IntermediateField Submodule

namespace FrobeniusClosedBasis

variable {k : Type*} {E : Type v} [Field k] [Field E] [Algebra k E]

/-- An element which is both a polynomial in a transcendental `y` and a polynomial in `y⁻¹` is a
constant. -/
theorem exists_algebraMap_eq_of_aeval_eq_aeval_inv {y c : E} (hy : Transcendental k y)
    {q₁ q₂ : k[X]} (h₁ : aeval y q₁ = c) (h₂ : aeval y⁻¹ q₂ = c) :
    ∃ a, algebraMap k E a = c := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy isAlgebraic_zero
  let := invertibleOfNonzero (inv_ne_zero hy0)
  have hrefl : aeval y (reflect q₂.natDegree q₂) = aeval y (q₁ * X ^ q₂.natDegree) := by
    have := eval₂_reflect_mul_pow (algebraMap k E) y⁻¹ q₂.natDegree q₂ le_rfl
    rw [invOf_eq_inv, inv_inv, ← aeval_def, ← aeval_def, h₂] at this
    rw [map_mul, h₁, map_pow, aeval_X, ← this, mul_assoc, ← mul_pow, inv_mul_cancel₀ hy0,
      one_pow, mul_one]
  have heq := transcendental_iff_injective.1 hy hrefl
  have hdeg : (q₁ * X ^ q₂.natDegree).natDegree ≤ q₂.natDegree :=
    heq ▸ natDegree_reflect_le.trans (max_le le_rfl le_rfl)
  have h0 : q₁.natDegree = 0 := by
    rcases eq_or_ne q₁ 0 with rfl | hq
    · simp
    · rw [natDegree_mul_X_pow _ hq] at hdeg
      omega
  refine ⟨q₁.coeff 0, ?_⟩
  rw [← h₁, ← aeval_C y (q₁.coeff 0), ← eq_C_of_natDegree_eq_zero h0]

/-- **Frobenius-closed bases** (Kuhlmann, Theorem 10 / Lemma 26). Let `k` be an algebraically
closed field of characteristic `p`, and `E` a finite separable extension of `k⟮x⟯` with `x`
transcendental over `k`. Then there is a family `w : ι → E` such that `1` together with the
`w i ^ p ^ r` (`i : ι`, `r : ℕ`) form a `k`-basis of `E`. -/
theorem exists_frobeniusClosed_basis (k : Type*) [Field k] [Algebra k E] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP E p] (x : E) (hx : Transcendental k x)
    [FiniteDimensional k⟮x⟯ E] [Algebra.IsSeparable k⟮x⟯ E] :
    ∃ (ι : Type v) (w : ι → E),
      LinearIndependent k (fun j : Option (ι × ℕ) ↦ j.elim 1 (fun i ↦ w i.1 ^ p ^ i.2)) ∧
      span k (Set.range (fun j : Option (ι × ℕ) ↦ j.elim 1 (fun i ↦ w i.1 ^ p ^ i.2))) = ⊤ := by
  have hp := (Fact.out : p.Prime)
  have hxinv : Transcendental k x⁻¹ := fun h ↦ hx (IsAlgebraic.inv_iff.1 h)
  have hK : k⟮x⁻¹⟯ = k⟮x⟯ :=
    le_antisymm (adjoin_simple_le_iff.2 (inv_mem (mem_adjoin_simple_self k x)))
      (adjoin_simple_le_iff.2 (by simpa using inv_mem (mem_adjoin_simple_self k x⁻¹)))
  obtain ⟨J₁, v₁, h1₁, hfin₁, hint₁⟩ := exists_valuations_of_transcendental k x hx k⟮x⟯ rfl
  obtain ⟨J₂, v₂, h1₂, hfin₂, hint₂⟩ := exists_valuations_of_transcendental k x⁻¹ hxinv k⟮x⟯ hK
  refine exists_frobeniusClosed_basis_of_valuations p
    (fun c ↦ IsAlgClosed.exists_pow_nat_eq c hp.pos) (Sum.elim v₁ v₂) ?_ ?_ ?_
  · rintro (j | j) c hc
    · exact h1₁ j c hc
    · exact h1₂ j c hc
  · intro f
    obtain ⟨n₁, hn₁⟩ := exists_bound_of_finite v₁ f (hfin₁ f)
    obtain ⟨n₂, hn₂⟩ := exists_bound_of_finite v₂ f (hfin₂ f)
    refine ⟨max n₁ n₂, ?_⟩
    rintro (j | j)
    · exact (hn₁ j).trans (WithZero.exp_le_exp.2 (Nat.cast_le.2 (le_max_left _ _)))
    · exact (hn₂ j).trans (WithZero.exp_le_exp.2 (Nat.cast_le.2 (le_max_right _ _)))
  · intro f hf
    have hc (i : ℕ) : ((minpoly k⟮x⟯ f).coeff i : E) ∈ Set.range (algebraMap k E) := by
      obtain ⟨q₁, h₁⟩ := hint₁ f (fun j ↦ hf (Sum.inl j)) i
      obtain ⟨q₂, h₂⟩ := hint₂ f (fun j ↦ hf (Sum.inr j)) i
      exact exists_algebraMap_eq_of_aeval_eq_aeval_inv hx h₁.symm h₂.symm
    have hmon := minpoly.monic (Algebra.IsIntegral.isIntegral (R := k⟮x⟯) f)
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic
      ((lifts_iff_coeff_lifts _).2 fun n ↦ by rw [coeff_map]; exact hc n)
      (hmon.map (algebraMap k⟮x⟯ E))
    have hint : IsIntegral k f :=
      ⟨q, hqm, by rw [← eval_map, hq, eval_map, ← aeval_def, minpoly.aeval]⟩
    exact RingHom.mem_range.1 (minpoly.mem_range_of_degree_eq_one k f
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)))

/-- **Kuhlmann, Lemma 25.** Given a Frobenius-closed basis `1, w i ^ p ^ r` of `E` over `k`, if
`c₀ + ∑ i ∈ s, c i • w i` is a `p`-th power in `E`, then all `c i` (`i ∈ s`) vanish. -/
theorem eq_zero_of_add_sum_eq_pow {E : Type*} [Field E] [Algebra k E] (p : ℕ)
    [Fact p.Prime] [CharP E p] {ι : Type*} {w : ι → E}
    (hli : LinearIndependent k (fun j : Option (ι × ℕ) ↦ j.elim 1 (fun i ↦ w i.1 ^ p ^ i.2)))
    (hsp : span k (Set.range (fun j : Option (ι × ℕ) ↦ j.elim 1 (fun i ↦ w i.1 ^ p ^ i.2))) = ⊤)
    (s : Finset ι) (c : ι → k) (c₀ : k) (z : E)
    (h : algebraMap k E c₀ + ∑ i ∈ s, c i • w i = z ^ p) : ∀ i ∈ s, c i = 0 := by
  classical
  have hp := (Fact.out : p.Prime)
  let b := Module.Basis.mk hli hsp.ge
  have hb (j : Option (ι × ℕ)) : b j = j.elim 1 (fun i ↦ w i.1 ^ p ^ i.2) :=
    Module.Basis.mk_apply _ _ _
  have hz : z ^ p ∈ span k (b '' {j | ∀ i, j ≠ some (i, 0)}) := by
    refine pow_mem_span_of_pow_mem (s := Set.range b) (fun x hx ↦ ?_) (b.mem_span z)
    obtain ⟨_ | ⟨i, r⟩, rfl⟩ := hx
    · exact subset_span ⟨none, by simp, by simp [hb]⟩
    · exact subset_span ⟨some (i, r + 1), by simp, by simp [hb, pow_succ, pow_mul]⟩
  intro i hi
  have h2 : b.repr (z ^ p) (some (i, 0)) = 0 := by
    by_contra hne
    exact b.mem_span_image.1 hz (Finsupp.mem_support_iff.2 hne) i rfl
  have hw (i : ι) : w i = b (some (i, 0)) := by simp [hb]
  have h1 : (1 : E) = b none := by simp [hb]
  rw [← h, Algebra.algebraMap_eq_smul_one, h1] at h2
  simp_rw [hw] at h2
  simpa [Finsupp.single_apply, hi] using h2

end FrobeniusClosedBasis
