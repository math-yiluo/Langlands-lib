import Langlands.Correspondence.SegmentEpsilonAlgebra
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial LocalFactor RationalEvaluation

/-- A normalized product polynomial divisible by the actual L-polynomial cannot
lose a root to its reflected dual product when the two root sets are separated. -/
theorem eq_of_separated_rationalGammaExpression
    {δ : ℂˣ} {e e' : ℂˣ × ℤ} {P D B BD Q : ℂ[X]}
    (hP : P.coeff 0 = 1) (hD : D.coeff 0 = 1) (hBD : BD.coeff 0 = 1)
    (hQ : Q.coeff 0 = 1) (hB : B = Q * P)
    (hsep : ∀ x : ℂ, x ≠ 0 → B.eval x = 0 → BD.eval ((δ : ℂ) / x) ≠ 0)
    (hgamma : rationalGammaExpression δ e'.1 e'.2 B BD =
      rationalGammaExpression δ e.1 e.2 P D) : P = B ∧ e = e' := by
  have hP0 : P ≠ 0 := fun h => by simp [h] at hP
  have href (A : ℂ[X]) (hA : A.coeff 0 = 1) :
      aeval (RationalReflection.reflectedVariable δ) A ≠ 0 := by
    rw [← RationalReflection.subst_polynomial]
    exact (map_ne_zero_iff _ (RationalReflection.equiv δ).injective).mpr
      (RatFunc.algebraMap_ne_zero (fun h => by simp [h] at hA))
  have hdeg : Q.degree ≤ 0 := by
    by_contra hn
    obtain ⟨x, hxQ⟩ := Complex.exists_root (lt_of_not_ge hn)
    have hx : x ≠ 0 := by
      intro h
      subst x
      simp [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, hQ] at hxQ
    have hxB : B.eval x = 0 := by simp [hB, show Q.eval x = 0 from hxQ]
    have hc := hgamma
    unfold rationalGammaExpression at hc
    rw [div_eq_div_iff (href BD hBD) (href D hD), hB, map_mul] at hc
    have h := mul_left_cancel₀ (RatFunc.algebraMap_ne_zero hP0) (show
        algebraMap ℂ[X] (RatFunc ℂ) P *
          ((rationalEpsilonMonomial e'.1 e'.2 : RatFunc ℂ) *
            algebraMap ℂ[X] (RatFunc ℂ) Q * aeval (RationalReflection.reflectedVariable δ) D) =
        algebraMap ℂ[X] (RatFunc ℂ) P *
          ((rationalEpsilonMonomial e.1 e.2 : RatFunc ℂ) *
            aeval (RationalReflection.reflectedVariable δ) BD) by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hc)
    have h' := congrArg (RatFunc.eval (RingHom.id ℂ) x) h
    have he := regular_rationalEpsilonMonomial e.1 e.2 hx
    have he' := regular_rationalEpsilonMonomial e'.1 e'.2 hx
    have hq := RegularAt.polynomial (z := x) Q
    have hr := regular_reflectedVariable δ hx
    rw [RationalEvaluation.eval_mul (he'.mul hq) (hr.aeval D),
      RationalEvaluation.eval_mul he' hq, RationalEvaluation.eval_mul he (hr.aeval BD),
      eval_rationalEpsilonMonomial e.1 e.2 hx, eval_aeval hr BD,
      eval_reflectedVariable δ hx] at h'
    have hz : 0 = (((e.1 : ℂ) * x ^ e.2) * BD.eval ((δ : ℂ) / x)) := by
      simpa [show Q.eval x = 0 from hxQ] using h'
    exact (mul_ne_zero (mul_ne_zero e.1.ne_zero (zpow_ne_zero _ hx)) (hsep x hx hxB)) hz.symm
  have hQ1 : Q = 1 := by simpa [hQ] using Polynomial.eq_C_of_degree_le_zero hdeg
  have hPB : P = B := by simpa [hQ1] using hB.symm
  refine ⟨hPB, ?_⟩
  rw [← hPB] at hgamma
  obtain ⟨hcoeff, hexp⟩ := rationalGammaExpression_cancel hP0 hD hBD hgamma.symm
  exact Prod.ext hcoeff hexp

end Langlands.RankinSelberg
