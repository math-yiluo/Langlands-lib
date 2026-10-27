import Langlands.Automorphic.Unramified.TraceAlgebraStatement
import Langlands.Automorphic.Unramified.PolynomialTraceGeneratingSeriesProof
import Langlands.Automorphic.Unramified.MatrixTraceGeneratingSeriesProof
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace Langlands.Automorphic.Unramified

private theorem expand_inv (P : PowerSeries ℂ) (hP : P.constantCoeff ≠ 0)
    (f : ℕ) (hf : f ≠ 0) :
    PowerSeries.expand f hf P⁻¹ = (PowerSeries.expand f hf P)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simpa using hP)).2
  rw [← map_mul, PowerSeries.inv_mul_cancel P hP, map_one]

private theorem euler_derivative_expand (P : PowerSeries ℂ) (f : ℕ) (hf : f ≠ 0) :
    PowerSeries.X * PowerSeries.derivative (PowerSeries.expand f hf P) =
      PowerSeries.C (f : ℂ) *
        PowerSeries.expand f hf (PowerSeries.X * PowerSeries.derivative P) := by
  rw [PowerSeries.expand_apply, PowerSeries.derivative_subst (PowerSeries.HasSubst.X_pow hf),
    PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one,
    map_mul, PowerSeries.expand_X, PowerSeries.expand_apply]
  have hx : (PowerSeries.X : PowerSeries ℂ) * PowerSeries.X ^ (f - 1) =
      PowerSeries.X ^ f := by rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hf)]
  rw [map_natCast]
  calc
    _ = (f : PowerSeries ℂ) *
        (PowerSeries.X * PowerSeries.X ^ (f - 1)) *
        (PowerSeries.derivative P).subst (PowerSeries.X ^ f) := by ring
    _ = _ := by rw [hx, mul_assoc]

private theorem coe_comp_X_pow (P : Polynomial ℂ) (f : ℕ) (hf : f ≠ 0) :
    ((P.comp (Polynomial.X ^ f) : Polynomial ℂ) : PowerSeries ℂ) =
      PowerSeries.expand f hf (P : PowerSeries ℂ) := by
  ext k
  rw [Polynomial.coeff_coe, PowerSeries.coeff_expand]
  simpa only [Polynomial.expand_eq_comp_X_pow, Polynomial.coeff_coe] using
    Polynomial.coeff_expand (R := ℂ) (Nat.pos_of_ne_zero hf) P k

private theorem negative_log_derivative_expand (P : PowerSeries ℂ)
    (hP : P.constantCoeff ≠ 0) (f : ℕ) (hf : f ≠ 0) :
    -PowerSeries.X * PowerSeries.derivative (PowerSeries.expand f hf P) *
        (PowerSeries.expand f hf P)⁻¹ =
      PowerSeries.C (f : ℂ) * PowerSeries.expand f hf
        (-PowerSeries.X * PowerSeries.derivative P * P⁻¹) := by
  rw [neg_mul, euler_derivative_expand, ← expand_inv P hP f hf]
  simp only [map_mul, map_neg]
  ring

private theorem coeff_negative_log_derivative_expand (P : PowerSeries ℂ)
    (hP : P.constantCoeff ≠ 0) (f : ℕ) (hf : f ≠ 0) (k : ℕ) :
    PowerSeries.coeff k
      (-PowerSeries.X * PowerSeries.derivative (PowerSeries.expand f hf P) *
        (PowerSeries.expand f hf P)⁻¹) =
      if f ∣ k then (f : ℂ) * PowerSeries.coeff (k / f)
        (-PowerSeries.X * PowerSeries.derivative P * P⁻¹) else 0 := by
  rw [negative_log_derivative_expand P hP f hf, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_expand]
  split_ifs <;> simp


/-- The complete polynomial-substitution and weighted-power-trace equivalence. -/
theorem inductionPolynomialTrace : InductionPolynomialTraceStatement := by
  classical
  intro a m n f A B hf
  have hA (i : Fin a) : (A i).charpolyRev.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have hB : B.charpolyRev.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have hcomp (i : Fin a) : ((A i).charpolyRev.comp (Polynomial.X ^ f i)).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
    simp [Nat.ne_of_gt (hf i)]
  have hP : (∏ i, (A i).charpolyRev.comp (Polynomial.X ^ f i)).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    simp only [← Polynomial.coeff_zero_eq_eval_zero, hcomp, Finset.prod_const_one]
  have hsubst (i : Fin a) (k : ℕ) :
      PowerSeries.coeff k (polynomialTraceSeries ((A i).charpolyRev.comp (Polynomial.X ^ f i))) =
        if f i ∣ k then (f i : ℂ) * PowerSeries.coeff (k / f i) (polynomialTraceSeries (A i).charpolyRev)
        else 0 := by
    simp only [polynomialTraceSeries]
    rw [coe_comp_X_pow _ _ (Nat.ne_of_gt (hf i))]
    exact coeff_negative_log_derivative_expand _ (by simp [hA i]) _ _ _
  have hsum (k : ℕ) (hk : 0 < k) :
      PowerSeries.coeff k (polynomialTraceSeries (∏ i, (A i).charpolyRev.comp (Polynomial.X ^ f i))) =
        ∑ i, if f i ∣ k then
          (f i : ℂ) * Matrix.trace ((A i) ^ (k / f i)) else 0 := by
    rw [polynomialTraceGeneratingSeries.2 _ _ hcomp, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsubst]
    split_ifs with hdiv
    · rw [matrixTraceGeneratingSeries _ _ _ (Nat.div_pos (Nat.le_of_dvd hk hdiv) (hf i))]
    · rfl
  constructor
  · intro heq k hk
    rw [← matrixTraceGeneratingSeries m B k hk, heq, hsum k hk]
  · intro heq
    apply (polynomialTraceGeneratingSeries.1 _ _ hB hP).mp
    ext k
    obtain rfl | hk := Nat.eq_zero_or_pos k
    · simp [polynomialTraceSeries]
    · rw [matrixTraceGeneratingSeries m B k hk, hsum k hk, heq k hk]

end Langlands.Automorphic.Unramified
