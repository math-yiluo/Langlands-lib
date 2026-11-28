import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Kloosterman sums over a finite field

For a finite field `k`, a complex additive character `ψ` of `k`, `n : ℕ` and `A ∈ k`, the
`n`-variable Kloosterman sum is
`Kl_n(ψ, A) = Σ_{s ∈ kⁿ, s₁ ⋯ sₙ = A} ψ(s₁ + ⋯ + sₙ)`.
If `ψ` is nontrivial, the sum of `Kl_n(ψ, A)` over `A ≠ 0` is `(-1)ⁿ`, so some `Kl_n(ψ, A)`
with `A ≠ 0` is nonzero. Averaging `ψ(Σ rᵢ cᵢ)` over the `r ∈ kⁿ` with `r₁ ⋯ rₙ = 1` gives
`Kl_n(ψ, c₁ ⋯ cₙ)` when every `cᵢ` is nonzero.
-/

noncomputable section

namespace Langlands.AffineGeneric

open Finset

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

/-- The `n`-variable Kloosterman sum `Kl_n(ψ, A) = Σ_{s₁ ⋯ sₙ = A} ψ(s₁ + ⋯ + sₙ)`. -/
def kloosterman (ψ : AddChar k ℂ) (n : ℕ) (A : k) : ℂ :=
  ∑ s : Fin n → k, if ∏ i, s i = A then ψ (∑ i, s i) else 0

omit [Fintype k] [DecidableEq k] in
/-- An additive character turns finite sums into products. -/
theorem addChar_sum {ι : Type*} (ψ : AddChar k ℂ) (s : Finset ι) (f : ι → k) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- The sum of a nontrivial character over the nonzero elements of `k` is `-1`. -/
theorem sum_ite_ne_zero (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) :
    ∑ t : k, (if t ≠ 0 then ψ t else 0) = -1 := by
  classical
  have h := AddChar.sum_eq_zero_of_ne_one hψ
  rw [← Finset.sum_filter, Finset.filter_ne' univ (0 : k), Finset.sum_erase_eq_sub (mem_univ 0),
    h, AddChar.map_zero_eq_one, zero_sub]

/-- **The sum of the Kloosterman sums.** For a nontrivial `ψ`,
`Σ_{A ≠ 0} Kl_n(ψ, A) = (-1)ⁿ`. -/
theorem sum_kloosterman (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (n : ℕ) :
    ∑ A ∈ univ.erase (0 : k), kloosterman ψ n A = (-1) ^ n := by
  unfold kloosterman
  rw [Finset.sum_comm]
  have h1 : ∀ s : Fin n → k,
      (∑ A ∈ univ.erase (0 : k), if ∏ i, s i = A then ψ (∑ i, s i) else 0) =
        ∏ i, (if s i ≠ 0 then ψ (s i) else 0) := by
    intro s
    rw [Finset.sum_ite_eq, Fintype.prod_ite_zero, addChar_sum]
    simp only [mem_erase, mem_univ, and_true, ne_eq, Finset.prod_eq_zero_iff, not_exists,
      not_and]
    simp
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (_ : Fin n) (t : k) => if t ≠ 0 then ψ t else 0),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, sum_ite_ne_zero ψ hψ]

/-- For a nontrivial `ψ`, some Kloosterman sum `Kl_n(ψ, A)` with `A ≠ 0` is nonzero. -/
theorem exists_kloosterman_ne_zero (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (n : ℕ) :
    ∃ A : k, A ≠ 0 ∧ kloosterman ψ n A ≠ 0 := by
  by_contra! h
  have hs := sum_kloosterman ψ hψ n
  rw [Finset.sum_eq_zero fun A hA => h A (Finset.ne_of_mem_erase hA)] at hs
  exact pow_ne_zero n (neg_ne_zero.mpr one_ne_zero) hs.symm

/-- **Averaging over the norm-one torus.** If every `cᵢ` is nonzero, then
`Σ_{r₁ ⋯ rₙ = 1} ψ(Σ rᵢ cᵢ) = Kl_n(ψ, c₁ ⋯ cₙ)`. -/
theorem sum_prod_eq_one (ψ : AddChar k ℂ) {n : ℕ} {c : Fin n → k} (hc : ∀ i, c i ≠ 0) :
    ∑ r ∈ univ.filter (fun r : Fin n → k => ∏ i, r i = 1), ψ (∑ i, r i * c i) =
      kloosterman ψ n (∏ i, c i) := by
  rw [Finset.sum_filter]
  unfold kloosterman
  let e : (Fin n → k) ≃ (Fin n → k) :=
    { toFun := fun r i => r i * c i
      invFun := fun s i => s i * (c i)⁻¹
      left_inv := fun r => by
        funext i
        simp [mul_assoc, mul_inv_cancel₀ (hc i)]
      right_inv := fun s => by
        funext i
        simp [mul_assoc, inv_mul_cancel₀ (hc i)] }
  refine Fintype.sum_equiv e _ _ fun r => ?_
  have hcp : ∏ i, c i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hc i
  have hiff : (∏ i, r i = 1) ↔ ∏ i, e r i = ∏ i, c i := by
    simp only [e, Equiv.coe_fn_mk, Finset.prod_mul_distrib]
    constructor
    · intro h
      rw [h, one_mul]
    · intro h
      exact (mul_eq_right₀ hcp).mp h
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl

omit [DecidableEq k] in
/-- A finite field carries a nontrivial complex additive character. -/
theorem exists_addChar_ne_one : ∃ ψ : AddChar k ℂ, ψ ≠ 1 := by
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : k))).mpr one_ne_zero
  exact ⟨ψ, fun h => hψ (by rw [h, AddChar.one_apply])⟩

end Langlands.AffineGeneric
