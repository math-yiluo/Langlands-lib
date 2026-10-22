import Langlands.LocalFactor.WeilDelignePair
import Mathlib.FieldTheory.RatFunc.AsPolynomial

noncomputable section

namespace Langlands.RankinSelberg.RationalEvaluation

open Polynomial LocalFactor

universe u
variable {K : Type u} [Field K] {z : K} {R S : RatFunc K}

/-- The reduced denominator does not vanish at the evaluation point. -/
def RegularAt (R : RatFunc K) (z : K) : Prop := R.denom.eval z ≠ 0

theorem RegularAt.of_dvd {P : K[X]} (hP : P.eval z ≠ 0)
    (h : R.denom ∣ P) : RegularAt R z := by
  intro hz
  exact hP (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero h hz)

theorem RegularAt.polynomial (P : K[X]) :
    RegularAt (algebraMap K[X] (RatFunc K) P) z := by
  simp [RegularAt]

theorem RegularAt.add (hR : RegularAt R z) (hS : RegularAt S z) :
    RegularAt (R + S) z :=
  RegularAt.of_dvd (by simpa using mul_ne_zero hR hS) (RatFunc.denom_add_dvd R S)

theorem RegularAt.mul (hR : RegularAt R z) (hS : RegularAt S z) :
    RegularAt (R * S) z :=
  RegularAt.of_dvd (by simpa using mul_ne_zero hR hS) (RatFunc.denom_mul_dvd R S)

theorem eval_add (hR : RegularAt R z) (hS : RegularAt S z) :
    RatFunc.eval (RingHom.id K) z (R + S) =
      RatFunc.eval (RingHom.id K) z R + RatFunc.eval (RingHom.id K) z S := by
  exact RatFunc.eval_add (RingHom.id K) z (by simpa [RegularAt] using hR) (by simpa [RegularAt] using hS)

theorem eval_mul (hR : RegularAt R z) (hS : RegularAt S z) :
    RatFunc.eval (RingHom.id K) z (R * S) =
      RatFunc.eval (RingHom.id K) z R * RatFunc.eval (RingHom.id K) z S := by
  exact RatFunc.eval_mul (RingHom.id K) z (by simpa [RegularAt] using hR) (by simpa [RegularAt] using hS)

theorem RegularAt.of_eval_ne_zero (h : RatFunc.eval (RingHom.id K) z R ≠ 0) :
    RegularAt R z := by
  simpa [RegularAt] using RatFunc.eval₂_denom_ne_zero h

theorem RegularAt.inv (h : RatFunc.eval (RingHom.id K) z R ≠ 0) :
    RegularAt R⁻¹ z := by
  have hR : R ≠ 0 := by intro hR; simp [hR] at h
  have hn : R.num.eval z ≠ 0 := by
    intro hn
    apply h
    simp [RatFunc.eval, hn]
  exact RegularAt.of_dvd hn (RatFunc.denom_inv_dvd hR)

theorem eval_inv (h : RatFunc.eval (RingHom.id K) z R ≠ 0) :
    RatFunc.eval (RingHom.id K) z R⁻¹ = (RatFunc.eval (RingHom.id K) z R)⁻¹ := by
  have hR : R ≠ 0 := by intro hR; simp [hR] at h
  have hm := eval_mul (RegularAt.of_eval_ne_zero h) (RegularAt.inv h)
  rw [mul_inv_cancel₀ hR, RatFunc.eval_one] at hm
  apply mul_left_cancel₀ h
  exact hm.symm.trans (mul_inv_cancel₀ h).symm

theorem eval_div (hR : RegularAt R z) (hS : RatFunc.eval (RingHom.id K) z S ≠ 0) :
    RatFunc.eval (RingHom.id K) z (R / S) =
      RatFunc.eval (RingHom.id K) z R / RatFunc.eval (RingHom.id K) z S := by
  rw [div_eq_mul_inv, eval_mul hR (RegularAt.inv hS), eval_inv hS, div_eq_mul_inv]

theorem RegularAt.pow (hR : RegularAt R z) (n : ℕ) : RegularAt (R ^ n) z := by
  induction n with
  | zero => simpa using (RegularAt.polynomial (z := z) (1 : K[X]))
  | succ n ih => simpa only [pow_succ] using ih.mul hR

theorem eval_pow (hR : RegularAt R z) (n : ℕ) :
    RatFunc.eval (RingHom.id K) z (R ^ n) = (RatFunc.eval (RingHom.id K) z R) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, eval_mul (hR.pow n) hR, ih, pow_succ]

theorem RegularAt.zpow (hR : RatFunc.eval (RingHom.id K) z R ≠ 0) (m : ℤ) :
    RegularAt (R ^ m) z := by
  cases m with
  | ofNat n => simpa using (RegularAt.of_eval_ne_zero hR).pow n
  | negSucc n =>
    simpa only [zpow_negSucc] using
      RegularAt.inv (by rw [eval_pow (RegularAt.of_eval_ne_zero hR)]; exact pow_ne_zero _ hR)

theorem eval_zpow (hR : RatFunc.eval (RingHom.id K) z R ≠ 0) (m : ℤ) :
    RatFunc.eval (RingHom.id K) z (R ^ m) = (RatFunc.eval (RingHom.id K) z R) ^ m := by
  cases m with
  | ofNat n => simpa using eval_pow (RegularAt.of_eval_ne_zero hR) n
  | negSucc n =>
    simp only [zpow_negSucc]
    rw [eval_inv (by rw [eval_pow (RegularAt.of_eval_ne_zero hR)]; exact pow_ne_zero _ hR),
      eval_pow (RegularAt.of_eval_ne_zero hR)]

theorem RegularAt.aeval (hR : RegularAt R z) (P : K[X]) :
    RegularAt (aeval R P) z := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_X, aeval_C]
    have ha : RegularAt (algebraMap K (RatFunc K) a) z := by
      simpa using (RegularAt.polynomial (z := z) (Polynomial.C a))
    exact ha.mul (hR.pow n)

theorem eval_aeval (hR : RegularAt R z) (P : K[X]) :
    RatFunc.eval (RingHom.id K) z (aeval R P) =
      P.eval (RatFunc.eval (RingHom.id K) z R) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, eval_add (hR.aeval P) (hR.aeval Q), hP, hQ, Polynomial.eval_add]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_X, aeval_C]
    have ha : RegularAt (algebraMap K (RatFunc K) a) z := by
      simpa using (RegularAt.polynomial (z := z) (Polynomial.C a))
    rw [eval_mul ha (hR.pow n), eval_pow hR]
    simp

theorem regular_reflectedVariable (c : Kˣ) (hz : z ≠ 0) :
    RegularAt (RationalReflection.reflectedVariable c) z := by
  have hc : RegularAt (algebraMap K (RatFunc K) (c : K)) z := by
    simpa using (RegularAt.polynomial (z := z) (Polynomial.C (c : K)))
  simpa only [RationalReflection.reflectedVariable, div_eq_mul_inv] using
    hc.mul (RegularAt.inv (R := RatFunc.X) (by simpa using hz))

theorem eval_reflectedVariable (c : Kˣ) (hz : z ≠ 0) :
    RatFunc.eval (RingHom.id K) z (RationalReflection.reflectedVariable c) = (c : K) / z := by
  unfold RationalReflection.reflectedVariable
  rw [eval_div (by simpa using (RegularAt.polynomial (z := z) (Polynomial.C (c : K))))
    (by simpa using hz)]
  simp

theorem regular_subst (c : Kˣ) (hz : z ≠ 0) (hR : RegularAt R ((c : K) / z)) :
    RegularAt (RationalReflection.subst c R) z := by
  conv_lhs => rw [← RatFunc.num_div_denom R, map_div₀,
    RationalReflection.subst_polynomial, RationalReflection.subst_polynomial]
  simp only [div_eq_mul_inv]
  exact ((regular_reflectedVariable c hz).aeval R.num).mul
    (RegularAt.inv (by
      rw [eval_aeval (regular_reflectedVariable c hz), eval_reflectedVariable c hz]
      exact hR))

theorem eval_subst (c : Kˣ) (hz : z ≠ 0) (hR : RegularAt R ((c : K) / z)) :
    RatFunc.eval (RingHom.id K) z (RationalReflection.subst c R) =
      RatFunc.eval (RingHom.id K) ((c : K) / z) R := by
  rw [← RatFunc.num_div_denom R, map_div₀,
    RationalReflection.subst_polynomial, RationalReflection.subst_polynomial]
  rw [eval_div ((regular_reflectedVariable c hz).aeval R.num) (by
    rw [eval_aeval (regular_reflectedVariable c hz), eval_reflectedVariable c hz]
    exact hR)]
  rw [eval_aeval (regular_reflectedVariable c hz),
    eval_aeval (regular_reflectedVariable c hz), eval_reflectedVariable c hz]
  rw [RatFunc.num_div_denom]
  rfl

end Langlands.RankinSelberg.RationalEvaluation
