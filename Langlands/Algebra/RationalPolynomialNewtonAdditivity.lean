import Langlands.Algebra.RationalPolynomialFiniteDifference

/-! # Additivity of the rational Newton transform -/

noncomputable section

open Polynomial Finset

namespace Langlands.Algebra.RationalPolynomial

/-- The finite Newton transform as an additive homomorphism on rational sequences. -/
def newtonPolynomialAddHom (d : ℕ) : (ℕ → ℚ) →+ Polynomial ℚ where
  toFun f := newtonPolynomial f d
  map_zero' := by
    unfold newtonPolynomial
    apply sum_eq_zero
    intro k _
    have hz : (fwdDiff 1)^[k] (0 : ℕ → ℚ) = 0 :=
      iterate_fwdDiff_eq_zero_of_le _ (r := 0) rfl (Nat.zero_le k)
    simp [hz]
  map_add' f g := by
    simp only [newtonPolynomial, fwdDiff_iter_add, Pi.add_apply, add_div,
      C_add, add_mul, sum_add_distrib]

@[simp]
theorem newtonPolynomial_zero (d : ℕ) :
    newtonPolynomial (0 : ℕ → ℚ) d = 0 :=
  (newtonPolynomialAddHom d).map_zero

theorem newtonPolynomial_add (f g : ℕ → ℚ) (d : ℕ) :
    newtonPolynomial (f + g) d = newtonPolynomial f d + newtonPolynomial g d :=
  (newtonPolynomialAddHom d).map_add f g

theorem newtonPolynomial_sub (f g : ℕ → ℚ) (d : ℕ) :
    newtonPolynomial (f - g) d = newtonPolynomial f d - newtonPolynomial g d :=
  (newtonPolynomialAddHom d).map_sub f g

theorem newtonPolynomial_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℚ) (d : ℕ) :
    newtonPolynomial (∑ i ∈ s, f i) d = ∑ i ∈ s, newtonPolynomial (f i) d :=
  map_sum (newtonPolynomialAddHom d) f s

end Langlands.Algebra.RationalPolynomial
