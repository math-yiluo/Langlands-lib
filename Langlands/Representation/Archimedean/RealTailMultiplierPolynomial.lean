import Langlands.Representation.Archimedean.RealBlockMultiplier
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! # Polynomial form of the differential tail multiplier -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealTailMultiplierPolynomial

open Polynomial RealBlockMultiplier

def argument (ℓ : ℕ) : ℂ[X] :=
  C (1 / 2 : ℂ) * (X + C ((ℓ : ℂ) - 1))

/-- The falling factorial at `(j+ell-1)/2`, divided by `ell!`. -/
def tailPolynomial (ℓ : ℕ) : ℂ[X] :=
  C ((ℓ.factorial : ℂ)⁻¹) * (descPochhammer ℂ ℓ).comp (argument ℓ)

theorem argument_natDegree (ℓ : ℕ) : (argument ℓ).natDegree = 1 := by
  rw [argument, natDegree_C_mul (by norm_num), natDegree_X_add_C]

theorem tailPolynomial_natDegree (ℓ : ℕ) : (tailPolynomial ℓ).natDegree = ℓ := by
  rw [tailPolynomial, natDegree_C_mul (inv_ne_zero (by exact_mod_cast ℓ.factorial_ne_zero)),
    natDegree_comp, descPochhammer_natDegree, argument_natDegree, mul_one]

theorem tailPolynomial_eval (ℓ : ℕ) (j : ℂ) :
    (tailPolynomial ℓ).eval j =
      (descPochhammer ℂ ℓ).eval ((j + (ℓ : ℂ) - 1) / 2) / (ℓ.factorial : ℂ) := by
  simp only [tailPolynomial, argument, eval_mul, eval_C, eval_comp, eval_add, eval_X]
  have hc : (1 / 2 : ℂ) * (j + ((ℓ : ℂ) - 1)) = (j + (ℓ : ℂ) - 1) / 2 := by ring
  rw [hc]
  ring

theorem tailPolynomial_neg (ℓ : ℕ) (j : ℂ) :
    (tailPolynomial ℓ).eval (-j) = (-1 : ℂ) ^ ℓ * (tailPolynomial ℓ).eval j := by
  rw [tailPolynomial_eval, tailPolynomial_eval,
    descPochhammer_eval_eq_ascPochhammer]
  have hc : (-j + (ℓ : ℂ) - 1) / 2 - (ℓ : ℂ) + 1 =
      -((j + (ℓ : ℂ) - 1) / 2) := by ring
  rw [hc, ascPochhammer_eval_neg_eq_descPochhammer]
  ring

theorem tailPolynomial_eq_of_nonneg {ℓ : ℕ} {ε j : ℤ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) (hj : 0 ≤ j) (hje : Even (j - ε)) :
    tailMultiplier ℓ ε ((-1 : ℂ) ^ ℓ) j = (tailPolynomial ℓ).eval (j : ℂ) := by
  have hεn : (ε.toNat : ℤ) = ε := Int.toNat_of_nonneg (by omega)
  have hja : (j.natAbs : ℤ) = j := by
    rw [Int.natCast_natAbs, abs_of_nonneg hj]
  have hi : (2 : ℤ) * ((j.natAbs / 2 + (ℓ - 1 + ε.toNat) / 2 : ℕ) : ℤ) =
      j + (ℓ : ℤ) - 1 := by
    rw [Int.even_iff] at hpar hje
    omega
  have hc : ((j.natAbs / 2 + (ℓ - 1 + ε.toNat) / 2 : ℕ) : ℂ) =
      ((j : ℂ) + (ℓ : ℂ) - 1) / 2 := by
    have hi' := congrArg (fun z : ℤ => (z : ℂ)) hi
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_sub,
      Int.cast_add, Int.cast_one] at hi'
    linear_combination hi' / 2
  rw [tailMultiplier, extend_of_nonneg hj, tailSeq,
    Nat.cast_choose_eq_descPochhammer_div, hc, tailPolynomial_eval]

/-- On its actual parity class, the tail with sign `(-1)^ell` is polynomial of degree ell. -/
theorem tailPolynomial_eq {ℓ : ℕ} {ε : ℤ}
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) (j : ℤ) (hje : Even (j - ε)) :
    tailMultiplier ℓ ε ((-1 : ℂ) ^ ℓ) j = (tailPolynomial ℓ).eval (j : ℂ) := by
  by_cases hj : 0 ≤ j
  · exact tailPolynomial_eq_of_nonneg hℓ hε hpar hj hje
  · have hneg : 0 ≤ -j := by omega
    have hje' : Even (-j - ε) := by
      rw [Int.even_iff] at hje ⊢
      omega
    have hp := tailPolynomial_eq_of_nonneg hℓ hε hpar hneg hje'
    have hs := isSymmetric_tailMultiplier hℓ hε hpar (neg_one_pow_sq ℓ) j hje
    apply mul_left_cancel₀ (pow_ne_zero ℓ (by norm_num : (-1 : ℂ) ≠ 0))
    rw [← hs, hp, Int.cast_neg, tailPolynomial_neg]

end Langlands.Archimedean.RealTailMultiplierPolynomial

namespace Langlands.Archimedean

open RealBlockMultiplier RealTailMultiplierPolynomial in
/-- The differential-sign tail is the explicit degree-ell polynomial on its parity class. -/
def RealTailMultiplierPolynomialStatement : Prop :=
  ∀ (ℓ : ℕ) (ε : ℤ), 0 < ℓ → (ε = 0 ∨ ε = 1) →
    Even ((ℓ : ℤ) - 1 - ε) →
    (tailPolynomial ℓ).natDegree = ℓ ∧
      ∀ j : ℤ, Even (j - ε) →
        tailMultiplier ℓ ε ((-1 : ℂ) ^ ℓ) j =
          (tailPolynomial ℓ).eval (j : ℂ)

theorem realTailMultiplierPolynomial : RealTailMultiplierPolynomialStatement :=
  fun ℓ _ hℓ hε hpar =>
    ⟨RealTailMultiplierPolynomial.tailPolynomial_natDegree ℓ,
      RealTailMultiplierPolynomial.tailPolynomial_eq hℓ hε hpar⟩

end Langlands.Archimedean
