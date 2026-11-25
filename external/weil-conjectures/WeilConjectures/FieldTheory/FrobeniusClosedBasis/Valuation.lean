/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import WeilConjectures.FieldTheory.FrobeniusClosedBasis.Filtration

/-!
# Frobenius-closed bases from a family of discrete valuations

Let `k` be a perfect field of characteristic `p` and `E ⊇ k` a field. Given a family of
`ℤᵐ⁰`-valued valuations on `E`, trivial on `k`, such that every element has bounded pole
orders and the elements without poles are exactly the constants, the pole-order filtration
satisfies the hypotheses of `FrobeniusClosedBasis.exists_frobeniusClosed_basis_of_filtration`,
so `E` has a Frobenius-closed `k`-basis.
-/

@[expose] public section

universe v

open Submodule
open scoped WithZero

namespace FrobeniusClosedBasis

variable {k : Type*} {E : Type v} [Field k] [Field E] [Algebra k E]

/-- The pole-order filtration attached to a family of valuations trivial on `k`: the elements
whose pole orders are all at most `n`. -/
def valuationFiltration {J : Type*} (v : J → Valuation E ℤᵐ⁰)
    (hv1 : ∀ j (c : k), c ≠ 0 → v j (algebraMap k E c) = 1) (n : ℕ) : Submodule k E where
  carrier := {f | ∀ j, v j f ≤ WithZero.exp (n : ℤ)}
  add_mem' hf hg j := (Valuation.map_add _ _ _).trans (max_le (hf j) (hg j))
  zero_mem' j := by simp
  smul_mem' c f hf j := by
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [Algebra.smul_def, map_mul, hv1 j c hc, one_mul]
      exact hf j

theorem mem_valuationFiltration {J : Type*} {v : J → Valuation E ℤᵐ⁰}
    {hv1 : ∀ j (c : k), c ≠ 0 → v j (algebraMap k E c) = 1} {n : ℕ} {f : E} :
    f ∈ valuationFiltration v hv1 n ↔ ∀ j, v j f ≤ WithZero.exp (n : ℤ) :=
  Iff.rfl

/-- If only finitely many valuations of a family have a pole at `f`, the pole orders of `f`
are bounded. -/
theorem exists_bound_of_finite {J : Type*} (v : J → Valuation E ℤᵐ⁰) (f : E)
    (hf : {j | 1 < v j f}.Finite) : ∃ n : ℕ, ∀ j, v j f ≤ WithZero.exp (n : ℤ) := by
  refine ⟨hf.toFinset.sup fun j ↦ (WithZero.log (v j f)).toNat, fun j ↦ ?_⟩
  by_cases hj : 1 < v j f
  · have hne : v j f ≠ 0 := (zero_lt_one.trans hj).ne'
    calc v j f = WithZero.exp (WithZero.log (v j f)) := (WithZero.exp_log hne).symm
      _ ≤ _ := WithZero.exp_le_exp.2 ((Int.self_le_toNat _).trans (Nat.cast_le.2
          (Finset.le_sup (f := fun j ↦ (WithZero.log (v j f)).toNat) (hf.mem_toFinset.2 hj))))
  · refine (not_lt.1 hj).trans ?_
    exact WithZero.exp_le_exp.2 (Nat.cast_nonneg _ : (0 : ℤ) ≤ _)

/-- **Frobenius-closed bases from valuations.** Let `k` be a perfect field of characteristic `p`
and `v` a family of valuations on the field `E ⊇ k`, trivial on `k`, such that the pole orders of
every element are bounded and every element without poles is a constant. Then there is a
family `w : ι → E` such that `1` together with the `w i ^ p ^ r` form a `k`-basis of `E`. -/
theorem exists_frobeniusClosed_basis_of_valuations (p : ℕ) [Fact p.Prime] [CharP E p]
    (hk : ∀ c : k, ∃ d, d ^ p = c) {J : Type*} (v : J → Valuation E ℤᵐ⁰)
    (hv1 : ∀ j (c : k), c ≠ 0 → v j (algebraMap k E c) = 1)
    (hfin : ∀ f, ∃ n : ℕ, ∀ j, v j f ≤ WithZero.exp (n : ℤ))
    (hint : ∀ f, (∀ j, v j f ≤ 1) → ∃ c, algebraMap k E c = f) :
    ∃ (ι : Type v) (w : ι → E),
      LinearIndependent k (fun j : Option (ι × ℕ) ↦ j.elim 1 (fun i ↦ w i.1 ^ p ^ i.2)) ∧
      span k (Set.range (fun j : Option (ι × ℕ) ↦ j.elim 1 (fun i ↦ w i.1 ^ p ^ i.2))) = ⊤ := by
  have hp := (Fact.out : p.Prime)
  refine exists_frobeniusClosed_basis_of_filtration p hk (valuationFiltration v hv1)
    (fun m n hmn f hf j ↦ (hf j).trans (WithZero.exp_le_exp.2 (Nat.cast_le.2 hmn)))
    hfin (fun j ↦ by simp) (fun f hf ↦ hint f fun j ↦ by simpa using hf j)
    (fun n f hf j ↦ ?_) (fun n f hf j ↦ ?_)
  · rw [map_pow, Nat.cast_mul, ← nsmul_eq_mul, WithZero.exp_nsmul]
    exact pow_le_pow_left₀ zero_le (hf j) p
  · have hfj := hf j
    rw [map_pow] at hfj
    rcases eq_or_ne (v j f) 0 with h0 | hne
    · rw [h0]
      exact zero_le
    · rw [← WithZero.exp_log hne] at hfj ⊢
      rw [← WithZero.exp_nsmul, WithZero.exp_le_exp, nsmul_eq_mul] at hfj
      rw [WithZero.exp_le_exp, Int.natCast_div]
      exact Int.le_ediv_of_mul_le (by exact_mod_cast hp.pos) (by linarith)

end FrobeniusClosedBasis
