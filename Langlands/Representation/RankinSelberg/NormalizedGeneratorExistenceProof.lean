import Langlands.Representation.RankinSelberg.NormalizedGeneratorExistenceStatement
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial

private theorem laurent_normalization (a : LaurentCoefficients) (ha : a ≠ 0) :
    ∃ P : ℂ[X], P.coeff 0 = 1 ∧
      ∃ u : LaurentCoefficientsˣ, a = (u : LaurentCoefficients) * P.toLaurent := by
  induction a using LaurentPolynomial.induction_on_mul_T with
  | mul_T p n =>
    have hp : p ≠ 0 := by
      intro hp
      simp [hp] at ha
    obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
    simp only [map_zero, sub_zero] at hpq hq
    have hc : q.coeff 0 ≠ 0 := by
      simpa only [Polynomial.X_dvd_iff] using hq
    let P : ℂ[X] := C (q.coeff 0)⁻¹ * q
    have hP : P.coeff 0 = 1 := by
      simp [P, Polynomial.mul_coeff_zero, hc]
    have hqP : q = C (q.coeff 0) * P := by
      simp [P, ← mul_assoc, ← map_mul, hc]
    have hu : IsUnit
        (LaurentPolynomial.T (p.rootMultiplicity 0 : ℤ) *
          LaurentPolynomial.C (q.coeff 0) * LaurentPolynomial.T (-(n : ℤ)) :
            LaurentCoefficients) :=
      ((LaurentPolynomial.isUnit_T _).mul
        ((isUnit_iff_ne_zero.mpr hc).map LaurentPolynomial.C)).mul
          (LaurentPolynomial.isUnit_T _)
    obtain ⟨u, hu⟩ := hu
    refine ⟨P, hP, u, ?_⟩
    rw [hu]
    conv_lhs =>
      rw [hpq, map_mul, Polynomial.toLaurent_X_pow, hqP,
        Polynomial.toLaurent_C_mul_eq]
    ring

/-- A fractional Laurent span containing one has a normalized reciprocal generator. -/
theorem normalizedGeneratorExistence : NormalizedGeneratorExistenceStatement := by
  intro values hden hone
  obtain ⟨g, hg⟩ := exists_rationalGenerator values hden
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hg ▸ hone)
  change laurentToRatFunc a * g = 1 at ha
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  obtain ⟨P, hP, u, hau⟩ := laurent_normalization a ha0
  refine ⟨P, hP, hg.trans ?_⟩
  apply Submodule.span_singleton_eq_span_singleton.mpr
  refine ⟨u, ?_⟩
  change laurentToRatFunc (u : LaurentCoefficients) * g =
    (algebraMap ℂ[X] RationalFunctions P)⁻¹
  apply eq_inv_of_mul_eq_one_left
  rw [hau, map_mul, laurentToRatFunc_toLaurent] at ha
  simpa only [mul_assoc, mul_left_comm, mul_comm] using ha

end Langlands.RankinSelberg
