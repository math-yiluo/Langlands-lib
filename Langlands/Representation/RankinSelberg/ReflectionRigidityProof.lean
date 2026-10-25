import Langlands.Representation.RankinSelberg.ReflectionRigidityStatement
import Langlands.Representation.RankinSelberg.RationalEvaluation
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace Langlands.RankinSelberg

open Polynomial LocalFactor RationalEvaluation

private theorem normalized_eq_one_of_no_roots (P : Polynomial ℂ)
    (hP : P.coeff 0 = 1) (hroots : ∀ z : ℂ, P.eval z ≠ 0) : P = 1 := by
  have hdeg : P.degree ≤ 0 := by
    by_contra h
    obtain ⟨z, hz⟩ := Complex.exists_root (lt_of_not_ge h)
    exact hroots z hz
  simpa [hP] using Polynomial.eq_C_of_degree_le_zero hdeg

/-- Reciprocal reflection and separated root regions force both normalized
polynomials to be one. -/
theorem reflectionRigidity : ReflectionRigidityStatement := by
  intro a b δ c m D E _ha hb hgap hD0 hE0 hD hE hidentity
  have heval (z : ℂ) (hz : z ≠ 0) :
      D.eval z = ((c : ℂ) * z ^ m) * E.eval ((δ : ℂ) / z) := by
    have hc : RegularAt (RatFunc.C (c : ℂ)) z :=
      RegularAt.of_eval_ne_zero (by simp)
    have hx : RatFunc.eval (RingHom.id ℂ) z RatFunc.X ≠ 0 := by simpa using hz
    have hm : RegularAt ((RatFunc.X : RatFunc ℂ) ^ m) z := RegularAt.zpow hx m
    have he := regular_subst δ hz (RegularAt.polynomial (z := (δ : ℂ) / z) E)
    have h := congrArg (RatFunc.eval (RingHom.id ℂ) z) hidentity
    rw [RationalEvaluation.eval_mul (hc.mul hm) he,
      RationalEvaluation.eval_mul hc hm, eval_zpow hx,
      eval_subst δ hz (RegularAt.polynomial E)] at h
    simpa using h
  have hDroots : ∀ z : ℂ, D.eval z ≠ 0 := by
    intro z hDz
    have hz : z ≠ 0 := by
      intro hz
      subst z
      simp [← Polynomial.coeff_zero_eq_eval_zero, hD0] at hDz
    have haz : a ≤ ‖z‖ := le_of_not_gt (fun h => hD z h hDz)
    have hEz : E.eval ((δ : ℂ) / z) = 0 := by
      have h := heval z hz
      rw [hDz] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero c.ne_zero (zpow_ne_zero m hz))
    have hbz : b ≤ ‖(δ : ℂ) / z‖ := le_of_not_gt (fun h => hE _ h hEz)
    have hprod : b * ‖z‖ ≤ ‖(δ : ℂ)‖ :=
      (le_div_iff₀ (norm_pos_iff.mpr hz)).mp (by simpa only [norm_div] using hbz)
    have hab : a * b ≤ ‖(δ : ℂ)‖ := by
      calc
        a * b ≤ ‖z‖ * b := mul_le_mul_of_nonneg_right haz hb.le
        _ = b * ‖z‖ := mul_comm _ _
        _ ≤ ‖(δ : ℂ)‖ := hprod
    exact (not_lt_of_ge hab) hgap
  have hDone : D = 1 := normalized_eq_one_of_no_roots D hD0 hDroots
  refine ⟨hDone, normalized_eq_one_of_no_roots E hE0 ?_⟩
  intro w hEw
  have hw : w ≠ 0 := by
    intro hw
    subst w
    simp [← Polynomial.coeff_zero_eq_eval_zero, hE0] at hEw
  have h := heval ((δ : ℂ) / w) (div_ne_zero δ.ne_zero hw)
  rw [div_div_cancel₀ δ.ne_zero, hEw, hDone] at h
  simp at h

end Langlands.RankinSelberg
