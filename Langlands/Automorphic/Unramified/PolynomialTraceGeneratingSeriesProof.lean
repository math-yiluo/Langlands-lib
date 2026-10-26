import Langlands.Automorphic.Unramified.TraceGeneratingSeriesStatement
import Mathlib.RingTheory.PowerSeries.Inverse

open scoped BigOperators
open Polynomial

namespace Langlands.Automorphic.Unramified

@[simp] theorem polynomialTraceSeries_coeff_zero (P : Polynomial ℂ) :
    PowerSeries.coeff 0 (polynomialTraceSeries P) = 0 := by
  simp [polynomialTraceSeries]

@[simp] theorem polynomialTraceSeries_one : polynomialTraceSeries 1 = 0 := by
  simp [polynomialTraceSeries]

theorem polynomialTraceSeries_mul (P Q : Polynomial ℂ)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    polynomialTraceSeries (P * Q) = polynomialTraceSeries P + polynomialTraceSeries Q := by
  have hPi : (P : PowerSeries ℂ) * (P : PowerSeries ℂ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [Polynomial.constantCoeff_coe, hP]; exact one_ne_zero)
  have hQi : (Q : PowerSeries ℂ) * (Q : PowerSeries ℂ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [Polynomial.constantCoeff_coe, hQ]; exact one_ne_zero)
  simp only [polynomialTraceSeries, Polynomial.coe_mul,
    MvPowerSeries.mul_inv_rev, Derivation.leibniz, smul_eq_mul]
  calc
    _ = (-PowerSeries.X * PowerSeries.derivative (P : PowerSeries ℂ) *
          (P : PowerSeries ℂ)⁻¹) * ((Q : PowerSeries ℂ) * (Q : PowerSeries ℂ)⁻¹) +
        (-PowerSeries.X * PowerSeries.derivative (Q : PowerSeries ℂ) *
          (Q : PowerSeries ℂ)⁻¹) * ((P : PowerSeries ℂ) * (P : PowerSeries ℂ)⁻¹) := by ring
    _ = _ := by rw [hPi, hQi]; ring

theorem polynomialTraceSeries_injective_normalized (P Q : Polynomial ℂ)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    polynomialTraceSeries P = polynomialTraceSeries Q ↔ P = Q := by
  constructor
  · intro h
    let p : PowerSeries ℂ := P
    let q : PowerSeries ℂ := Q
    have hp : PowerSeries.constantCoeff p = 1 := hP
    have hq : PowerSeries.constantCoeff q = 1 := hQ
    have hpi : p * p⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hp]; exact one_ne_zero)
    have hqi : q * q⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hq]; exact one_ne_zero)
    have hlog : PowerSeries.derivative p * p⁻¹ = PowerSeries.derivative q * q⁻¹ := by
      apply mul_left_cancel₀ (neg_ne_zero.mpr (PowerSeries.X_ne_zero (R := ℂ)))
      simpa only [polynomialTraceSeries, mul_assoc] using h
    have hcross : q * PowerSeries.derivative p = p * PowerSeries.derivative q := by
      calc
        _ = (PowerSeries.derivative p * p⁻¹) * (p * q) := by
          calc
            _ = (p * p⁻¹) * (q * PowerSeries.derivative p) := by rw [hpi, one_mul]
            _ = _ := by ring
        _ = (PowerSeries.derivative q * q⁻¹) * (p * q) := by rw [hlog]
        _ = p * PowerSeries.derivative q := by
          calc
            _ = (q * q⁻¹) * (p * PowerSeries.derivative q) := by ring
            _ = _ := by rw [hqi, one_mul]
    have hd : PowerSeries.derivative (p * q⁻¹) = PowerSeries.derivative (1 : PowerSeries ℂ) := by
      rw [Derivation.leibniz, PowerSeries.derivative_inv', PowerSeries.derivative_one,
        smul_eq_mul, smul_eq_mul]
      calc
        _ = q⁻¹ ^ 2 * (q * PowerSeries.derivative p - p * PowerSeries.derivative q) := by
          calc
            _ = (q * q⁻¹) * (q⁻¹ * PowerSeries.derivative p) -
                q⁻¹ ^ 2 * p * PowerSeries.derivative q := by rw [hqi, one_mul]; ring
            _ = _ := by ring
        _ = 0 := by rw [hcross, sub_self, mul_zero]
    have hratio : p * q⁻¹ = 1 := PowerSeries.derivative.ext hd (by simp [hp, hq])
    apply Polynomial.coe_injective ℂ
    change p = q
    calc
      p = (p * q⁻¹) * q := by
        calc
          _ = p * (q * q⁻¹) := by rw [hqi, mul_one]
          _ = _ := by ring
      _ = q := by rw [hratio, one_mul]
  · rintro rfl
    rfl

theorem polynomialTraceSeries_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → Polynomial ℂ) (hP : ∀ i ∈ s, (P i).coeff 0 = 1) :
    polynomialTraceSeries (∏ i ∈ s, P i) = ∑ i ∈ s, polynomialTraceSeries (P i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, polynomialTraceSeries_mul]
    · rw [ih (fun j hj => hP j (Finset.mem_insert_of_mem hj))]
    · exact hP i (Finset.mem_insert_self _ _)
    · rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
      exact Finset.prod_eq_one fun j hj => by
        rw [← Polynomial.coeff_zero_eq_eval_zero]
        exact hP j (Finset.mem_insert_of_mem hj)

/-- The complete published normalized-polynomial trace-series proposition. -/
theorem polynomialTraceGeneratingSeries :
    PolynomialTraceGeneratingSeriesStatement := by
  constructor
  · exact polynomialTraceSeries_injective_normalized
  · intro a P hP
    exact polynomialTraceSeries_prod Finset.univ P (fun i _ => hP i)

end Langlands.Automorphic.Unramified
