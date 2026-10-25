import Langlands.Representation.RankinSelberg.LaurentDivisibilityStatement

/-!
# Laurent-span criteria for polynomial divisibility

The three published algebraic criteria, using the Laurent action through
`laurentToRatFunc`. Denominator clearing and the coprimality calculation adapt
Worker 31's proofs in `RationalZeta`; no private declaration is used.
-/

noncomputable section

open Polynomial

namespace Langlands.RankinSelberg

/-- Clear a nonnegative power of `X` from reciprocal Laurent-span membership. -/
theorem reciprocalLaurentSpanClearing : ReciprocalLaurentSpanClearingStatement := by
  intro P A hP hA
  constructor
  · intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    change laurentToRatFunc a * (algebraMap ℂ[X] RationalFunctions A)⁻¹ =
      (algebraMap ℂ[X] RationalFunctions P)⁻¹ at ha
    have ha' := (mul_inv_eq_iff_eq_mul₀ (RatFunc.algebraMap_ne_zero hA)).mp ha
    have hamul : laurentToRatFunc a * algebraMap ℂ[X] RationalFunctions P =
        algebraMap ℂ[X] RationalFunctions A := by
      rw [ha', mul_right_comm, inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero hP),
        one_mul]
    obtain ⟨e, Q, hQ⟩ := LaurentPolynomial.exists_T_pow a
    have hmap : algebraMap ℂ[X] RationalFunctions (Q * P) =
        algebraMap ℂ[X] RationalFunctions (A * X ^ e) := by
      rw [map_mul, map_mul, map_pow, RatFunc.algebraMap_X]
      rw [← laurentToRatFunc_toLaurent Q, hQ, map_mul, laurentToRatFunc_T,
        zpow_natCast, mul_right_comm, hamul]
    have hpoly : Q * P = A * X ^ e := RatFunc.algebraMap_injective ℂ hmap
    exact ⟨Q, e, by simpa only [mul_comm] using hpoly.symm⟩
  · rintro ⟨Q, e, hpoly⟩
    have hmap : (RatFunc.X : RationalFunctions) ^ e *
        algebraMap ℂ[X] RationalFunctions A =
        algebraMap ℂ[X] RationalFunctions Q * algebraMap ℂ[X] RationalFunctions P := by
      simpa only [map_mul, map_pow, RatFunc.algebraMap_X] using
        congrArg (algebraMap ℂ[X] RationalFunctions) hpoly
    refine Submodule.mem_span_singleton.mpr
      ⟨Q.toLaurent * LaurentPolynomial.T (-(e : ℤ)), ?_⟩
    rw [Algebra.smul_def, algebraMap_laurent, map_mul, laurentToRatFunc_toLaurent,
      laurentToRatFunc_T, zpow_neg, zpow_natCast]
    apply mul_right_cancel₀ (RatFunc.algebraMap_ne_zero hP)
    calc
      (algebraMap ℂ[X] RationalFunctions Q * ((RatFunc.X : RationalFunctions) ^ e)⁻¹ *
          (algebraMap ℂ[X] RationalFunctions A)⁻¹) *
          algebraMap ℂ[X] RationalFunctions P =
          (algebraMap ℂ[X] RationalFunctions Q * algebraMap ℂ[X] RationalFunctions P) *
            (((RatFunc.X : RationalFunctions) ^ e)⁻¹ *
              (algebraMap ℂ[X] RationalFunctions A)⁻¹) := by ring
      _ = ((RatFunc.X : RationalFunctions) ^ e * algebraMap ℂ[X] RationalFunctions A) *
            (((RatFunc.X : RationalFunctions) ^ e)⁻¹ *
              (algebraMap ℂ[X] RationalFunctions A)⁻¹) := by rw [← hmap]
      _ = 1 := by
        rw [mul_mul_mul_comm, mul_inv_cancel₀ (pow_ne_zero e RatFunc.X_ne_zero),
          mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hA), mul_one]
      _ = (algebraMap ℂ[X] RationalFunctions P)⁻¹ *
          algebraMap ℂ[X] RationalFunctions P :=
        (inv_mul_cancel₀ (RatFunc.algebraMap_ne_zero hP)).symm

/-- Constant coefficient one removes the cleared power of `X`. -/
theorem normalizedReciprocalLaurentSpanDivisibility :
    NormalizedReciprocalLaurentSpanDivisibilityStatement := by
  intro P A hP hA
  have hP0 : P ≠ 0 := by
    intro hzero
    simp [hzero] at hP
  rw [reciprocalLaurentSpanClearing P A hP0 hA]
  constructor
  · rintro ⟨Q, e, hpoly⟩
    have hcop : IsCoprime P X := by
      refine ⟨1, -P.divX, ?_⟩
      have hx := Polynomial.X_mul_divX_add P
      rw [hP, Polynomial.C_1] at hx
      calc
        1 * P + -P.divX * X = P - X * P.divX := by ring
        _ = 1 := sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hx.symm)
    have hdvd : P ∣ A * X ^ e := by
      refine ⟨Q, ?_⟩
      simpa only [mul_comm] using hpoly
    exact hcop.pow_right.dvd_of_dvd_mul_right hdvd
  · rintro ⟨Q, hQ⟩
    exact ⟨Q, 0, by simpa only [pow_zero, one_mul] using hQ.trans (mul_comm P Q)⟩

/-- Inclusion of normalized reciprocal spans has the stated divisibility direction. -/
theorem normalizedGeneratorSpanDivisibility :
    NormalizedGeneratorSpanDivisibilityStatement := by
  intro S T P A hP hA
  rw [hP.2, hA.2, Submodule.span_singleton_le_iff_mem]
  exact normalizedReciprocalLaurentSpanDivisibility P A hP.1 hA.polynomial_ne_zero

/-- All three Laurent-span divisibility criteria, in their published order. -/
theorem laurentPolynomialDivisibility : LaurentPolynomialDivisibilityStatement :=
  ⟨reciprocalLaurentSpanClearing, normalizedReciprocalLaurentSpanDivisibility,
    normalizedGeneratorSpanDivisibility⟩

end Langlands.RankinSelberg
