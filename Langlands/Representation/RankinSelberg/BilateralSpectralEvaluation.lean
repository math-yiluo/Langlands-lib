import Langlands.HarmonicAnalysis.BilateralLaurentSeries
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Evaluation of convergent bilateral series and the actual finite Laurent action. -/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis

namespace BilateralSpectralEvaluation

/-- Absolute convergence of the actual integer-indexed weighted coefficient sum. -/
def AbsolutelySummableAt (x : ℂ) (a : BilateralLaurentSeries) : Prop :=
  Summable (fun m : ℤ => ‖a m * x ^ m‖)

/-- Reindexing a bilateral series by an integer shift multiplies its value by
the corresponding integer power of the nonzero evaluation point. -/
theorem hasSum_shift (x : ℂˣ) (a : BilateralLaurentSeries) (A : ℂ) (k : ℤ)
    (ha : HasSum (fun m : ℤ => a m * (x : ℂ) ^ m) A) :
    HasSum (fun m : ℤ => a (m - k) * (x : ℂ) ^ m) ((x : ℂ) ^ k * A) := by
  let e : ℤ ≃ ℤ :=
    { toFun := fun m => m - k
      invFun := fun m => m + k
      left_inv := fun m => by dsimp; omega
      right_inv := fun m => by dsimp; omega }
  have h := (e.hasSum_iff.mpr ha).mul_left ((x : ℂ) ^ k)
  have heq : (fun m : ℤ => (x : ℂ) ^ k * (a (e m) * (x : ℂ) ^ e m)) =
      (fun m : ℤ => a (m - k) * (x : ℂ) ^ m) := by
    funext m
    change (x : ℂ) ^ k * (a (m - k) * (x : ℂ) ^ (m - k)) =
      a (m - k) * (x : ℂ) ^ m
    calc
      _ = a (m - k) * ((x : ℂ) ^ k * (x : ℂ) ^ (m - k)) := by ring
      _ = _ := by rw [← zpow_add₀ (Units.ne_zero x), add_sub_cancel]
  exact heq ▸ h

/-- The actual finite Laurent convolution has the product of the two evaluated
values, with no support restriction on the bilateral input. -/
theorem hasSum_laurent_smul (x : ℂˣ) (P : LaurentPolynomial ℂ)
    (a : BilateralLaurentSeries) (A : ℂ)
    (ha : HasSum (fun m : ℤ => a m * (x : ℂ) ^ m) A) :
    HasSum (fun m : ℤ => (P • a) m * (x : ℂ) ^ m) (laurentEval x P * A) := by
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [add_smul, BilateralLaurentSeries.add_apply, add_mul, map_add] using hP.add hQ
  | C_mul_T k c =>
    have h := (hasSum_shift x a A k ha).mul_left c
    simpa only [BilateralLaurentSeries.C_mul_T_smul_apply, map_mul,
      laurentEval_C, laurentEval_T, mul_assoc] using h

/-- Laurent multiplication preserves weighted absolute convergence. -/
theorem absolutelySummableAt_laurent_smul (x : ℂˣ) (P : LaurentPolynomial ℂ)
    (a : BilateralLaurentSeries) (ha : AbsolutelySummableAt (x : ℂ) a) :
    AbsolutelySummableAt (x : ℂ) (P • a) := by
  have h := hasSum_laurent_smul x P a _ (summable_norm_iff.mp ha).hasSum
  exact summable_norm_iff.mpr h.summable

/-- The embedded coefficients of a finite Laurent polynomial have precisely
its ordinary evaluation as their bilateral sum. -/
theorem hasSum_ofLaurentPolynomial (x : ℂˣ) (P : LaurentPolynomial ℂ) :
    HasSum (fun m : ℤ => BilateralLaurentSeries.ofLaurentPolynomial P m * (x : ℂ) ^ m)
      (laurentEval x P) := by
  classical
  induction P using LaurentPolynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [map_add, BilateralLaurentSeries.add_apply, add_mul] using hP.add hQ
  | C_mul_T k c =>
    have heval : laurentEval x (LaurentPolynomial.C c * LaurentPolynomial.T k) =
        c * (x : ℂ) ^ k := by
      simp only [map_mul, laurentEval_C, laurentEval_T]
    simp only [heval]
    have hz : ∀ m ∉ ({k} : Finset ℤ),
        BilateralLaurentSeries.ofLaurentPolynomial
          (LaurentPolynomial.C c * LaurentPolynomial.T k) m * (x : ℂ) ^ m = 0 := by
      intro m hm
      have hmk : m ≠ k := by simpa using hm
      simp [BilateralLaurentSeries.ofLaurentPolynomial_apply,
        ← LaurentPolynomial.single_eq_C_mul_T, hmk]
    have h : HasSum (fun m : ℤ => BilateralLaurentSeries.ofLaurentPolynomial
        (LaurentPolynomial.C c * LaurentPolynomial.T k) m * (x : ℂ) ^ m)
        (∑ m ∈ ({k} : Finset ℤ), BilateralLaurentSeries.ofLaurentPolynomial
          (LaurentPolynomial.C c * LaurentPolynomial.T k) m * (x : ℂ) ^ m) :=
      hasSum_sum_of_ne_finset_zero hz
    simpa [BilateralLaurentSeries.ofLaurentPolynomial_apply,
      ← LaurentPolynomial.single_eq_C_mul_T] using h

theorem absolutelySummableAt_ofLaurentPolynomial (x : ℂˣ) (P : LaurentPolynomial ℂ) :
    AbsolutelySummableAt (x : ℂ) (BilateralLaurentSeries.ofLaurentPolynomial P) :=
  summable_norm_iff.mpr (hasSum_ofLaurentPolynomial x P).summable

/-- The summed finite convolution agrees with the product of the Laurent
evaluation and the original weighted sum. -/
theorem tsum_laurent_smul (x : ℂˣ) (P : LaurentPolynomial ℂ)
    (a : BilateralLaurentSeries) (ha : AbsolutelySummableAt (x : ℂ) a) :
    (∑' m : ℤ, (P • a) m * (x : ℂ) ^ m) =
      laurentEval x P * ∑' m : ℤ, a m * (x : ℂ) ^ m :=
  (hasSum_laurent_smul x P a _ (summable_norm_iff.mp ha).hasSum).tsum_eq

end BilateralSpectralEvaluation

end Langlands.RankinSelberg
