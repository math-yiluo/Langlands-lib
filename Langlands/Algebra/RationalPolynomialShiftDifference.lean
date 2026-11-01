import Langlands.Algebra.RationalPolynomialDilationProof
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! # Positive-step differences of rational polynomials -/

open Filter Polynomial

namespace Langlands.Algebra.RationalPolynomial

/-- The polynomial whose value at `x` is `P (x + e) - P x`. -/
noncomputable def shiftDifference (P : Polynomial ℚ) (e : ℚ) : Polynomial ℚ :=
  P.comp (X + C e) - P

@[simp]
theorem shiftDifference_eval (P : Polynomial ℚ) (e x : ℚ) :
    (shiftDifference P e).eval x = P.eval (x + e) - P.eval x := by
  simp [shiftDifference]

/-- A shift-difference identity on a natural-number tail determines the polynomial. -/
theorem eq_shiftDifference_of_eventually_nat_eval_eq (P Q : Polynomial ℚ) (e : ℕ)
    (h : ∀ᶠ n : ℕ in atTop,
      Q.eval (n : ℚ) = P.eval ((n + e : ℕ) : ℚ) - P.eval (n : ℚ)) :
    Q = shiftDifference P (e : ℚ) := by
  apply eq_of_eventually_nat_eval_eq
  exact h.mono fun n hn ↦ by simpa only [shiftDifference_eval, Nat.cast_add] using hn

/-- The coefficient just below a degree bound after translation and subtraction. -/
theorem shiftDifference_coeff (P : Polynomial ℚ) (e : ℚ) (d : ℕ)
    (hP : P.natDegree ≤ d + 1) :
    (shiftDifference P e).coeff d = ((d + 1 : ℕ) : ℚ) * e * P.coeff (d + 1) := by
  have hderiv : (hasseDeriv d P).natDegree ≤ 1 := by
    have := natDegree_hasseDeriv_le P d
    omega
  have hlinear := eq_X_add_C_of_natDegree_le_one hderiv
  change (P.comp (X + C e) - P).coeff d = _
  rw [coeff_sub, ← taylor_apply, taylor_coeff, hlinear]
  simp only [eval_add, eval_mul, eval_C, eval_X, hasseDeriv_coeff,
    zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  rw [Nat.add_comm 1 d, Nat.choose_succ_self_right]
  ring

/-- A positive top coefficient of a positive-step difference forces exact degree
and positive leading coefficient for the original polynomial. -/
theorem natDegree_eq_and_leadingCoeff_pos_of_shiftDifference
    (P : Polynomial ℚ) (e : ℚ) (d : ℕ) (he : 0 < e)
    (hP : P.natDegree ≤ d + 1)
    (hdeg : (shiftDifference P e).natDegree = d)
    (hpos : 0 < (shiftDifference P e).leadingCoeff) :
    P.natDegree = d + 1 ∧ 0 < P.leadingCoeff ∧
      (shiftDifference P e).leadingCoeff = ((d + 1 : ℕ) : ℚ) * e * P.leadingCoeff := by
  have hcoeff : 0 < ((d + 1 : ℕ) : ℚ) * e * P.coeff (d + 1) := by
    rw [← shiftDifference_coeff P e d hP, ← hdeg, coeff_natDegree]
    exact hpos
  have hfactor : 0 < ((d + 1 : ℕ) : ℚ) * e := mul_pos (by positivity) he
  have htop : 0 < P.coeff (d + 1) := (mul_pos_iff_of_pos_left hfactor).mp hcoeff
  have hdegree : P.natDegree = d + 1 :=
    Nat.le_antisymm hP (le_natDegree_of_ne_zero (ne_of_gt htop))
  have hlead : P.leadingCoeff = P.coeff (d + 1) := by
    rw [← hdegree, coeff_natDegree]
  refine ⟨hdegree, hlead ▸ htop, ?_⟩
  rw [hlead, ← shiftDifference_coeff P e d hP, ← hdeg, coeff_natDegree]

/-- The positive-natural-degree interface, with difference degree `d - 1`. -/
theorem natDegree_eq_and_leadingCoeff_pos_of_eventually_shiftDifference
    (P Q : Polynomial ℚ) (e d : ℕ) (he : 0 < e) (hd : 0 < d)
    (hP : P.natDegree ≤ d) (hdeg : Q.natDegree = d - 1)
    (hpos : 0 < Q.leadingCoeff)
    (h : ∀ᶠ n : ℕ in atTop,
      Q.eval (n : ℚ) = P.eval ((n + e : ℕ) : ℚ) - P.eval (n : ℚ)) :
    P.natDegree = d ∧ 0 < P.leadingCoeff ∧
      Q.leadingCoeff = (d : ℚ) * (e : ℚ) * P.leadingCoeff := by
  have hQ := eq_shiftDifference_of_eventually_nat_eval_eq P Q e h
  subst Q
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    natDegree_eq_and_leadingCoeff_pos_of_shiftDifference P (e : ℚ) d
      (by exact_mod_cast he) hP hdeg hpos

end Langlands.Algebra.RationalPolynomial
