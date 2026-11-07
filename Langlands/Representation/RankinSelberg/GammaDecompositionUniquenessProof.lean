import Langlands.Representation.RankinSelberg.GammaDecompositionUniquenessStatement
import Langlands.Representation.RankinSelberg.RationalEvaluation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.EuclideanDomain

namespace Langlands.RankinSelberg

open Polynomial LocalFactor RationalEvaluation

private theorem constant_of_no_roots (P : Polynomial ℂ)
    (hroots : ∀ z : ℂ, P.eval z ≠ 0) : P = C (P.coeff 0) := by
  apply Polynomial.eq_C_of_degree_le_zero
  by_contra h
  obtain ⟨z, hz⟩ := Complex.exists_root (lt_of_not_ge h)
  exact hroots z hz

/-- A normalized polynomial in a root-separated rational gamma decomposition is
unique without an assumed divisibility relation. -/
theorem gammaDecompositionUniqueness : GammaDecompositionUniquenessStatement := by
  classical
  intro a b δ c m P PD B BD _ha hb hgap hP0 hB0 hP hB hPD hBD hcross
  have hPne : P ≠ 0 := by
    intro h
    simp [h] at hP0
  have hBne : B ≠ 0 := by
    intro h
    simp [h] at hB0
  let g := gcd P B
  let D := P / g
  let E := B / g
  have hg : g ≠ 0 := gcd_ne_zero_of_left hPne
  have hPfactor : g * D = P := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left P B)
  have hBfactor : g * E = B := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right P B)
  have hDE : IsCoprime D E := isCoprime_div_gcd_div_gcd hBne
  have hgm : algebraMap ℂ[X] (RatFunc ℂ) g ≠ 0 := by
    intro h
    exact hg (RatFunc.algebraMap_injective ℂ (by simpa using h))
  have hcancel :
      algebraMap ℂ[X] (RatFunc ℂ) E *
          RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) PD) =
        (RatFunc.C (c : ℂ) * (RatFunc.X : RatFunc ℂ) ^ m) *
          algebraMap ℂ[X] (RatFunc ℂ) D *
            RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) BD) := by
    apply mul_left_cancel₀ hgm
    calc
      _ = algebraMap ℂ[X] (RatFunc ℂ) B *
          RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) PD) := by
            rw [← hBfactor, map_mul]
            ring
      _ = _ := hcross
      _ = _ := by
        rw [← hPfactor, map_mul]
        ring
  have heval (z : ℂ) (hz : z ≠ 0) :
      E.eval z * PD.eval ((δ : ℂ) / z) =
        ((c : ℂ) * z ^ m) * D.eval z * BD.eval ((δ : ℂ) / z) := by
    have hc : RegularAt (RatFunc.C (c : ℂ)) z :=
      RegularAt.of_eval_ne_zero (by simp)
    have hx : RatFunc.eval (RingHom.id ℂ) z RatFunc.X ≠ 0 := by simpa using hz
    have hm := RegularAt.zpow hx m
    have hd := regular_subst δ hz (RegularAt.polynomial (z := (δ : ℂ) / z) PD)
    have hbd := regular_subst δ hz (RegularAt.polynomial (z := (δ : ℂ) / z) BD)
    have h := congrArg (RatFunc.eval (RingHom.id ℂ) z) hcancel
    rw [RationalEvaluation.eval_mul (RegularAt.polynomial E) hd,
      RationalEvaluation.eval_mul ((hc.mul hm).mul (RegularAt.polynomial D)) hbd,
      RationalEvaluation.eval_mul (hc.mul hm) (RegularAt.polynomial D),
      RationalEvaluation.eval_mul hc hm, eval_zpow hx,
      eval_subst δ hz (RegularAt.polynomial PD),
      eval_subst δ hz (RegularAt.polynomial BD)] at h
    simpa using h
  have hreflect (z : ℂ) (hz : z ≠ 0) (haz : a ≤ ‖z‖) :
      ‖(δ : ℂ) / z‖ < b := by
    rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr hz)]
    calc
      ‖(δ : ℂ)‖ < a * b := hgap
      _ ≤ ‖z‖ * b := mul_le_mul_of_nonneg_right haz hb.le
      _ = b * ‖z‖ := mul_comm _ _
  have hDroots : ∀ z : ℂ, D.eval z ≠ 0 := by
    intro z hDz
    have hPz : P.eval z = 0 := by
      rw [← hPfactor, Polynomial.eval_mul, hDz, mul_zero]
    have hz : z ≠ 0 := by
      intro hz
      subst z
      simp [← coeff_zero_eq_eval_zero, hP0] at hPz
    have haz : a ≤ ‖z‖ := le_of_not_gt (fun h => hP z h hPz)
    have h := heval z hz
    rw [hDz, mul_zero, zero_mul] at h
    have hEz : E.eval z = 0 :=
      (mul_eq_zero.mp h).resolve_right (hPD _ (hreflect z hz haz))
    have hcop : D.eval z ≠ 0 ∨ E.eval z ≠ 0 := by
      simpa using Polynomial.aeval_ne_zero_of_isCoprime hDE z
    exact hcop.elim (fun hd => hd hDz) (fun he => he hEz)
  have hEroots : ∀ z : ℂ, E.eval z ≠ 0 := by
    intro z hEz
    have hBz : B.eval z = 0 := by
      rw [← hBfactor, Polynomial.eval_mul, hEz, mul_zero]
    have hz : z ≠ 0 := by
      intro hz
      subst z
      simp [← coeff_zero_eq_eval_zero, hB0] at hBz
    have haz : a ≤ ‖z‖ := le_of_not_gt (fun h => hB z h hBz)
    have h := heval z hz
    rw [hEz, zero_mul] at h
    have hDz : D.eval z = 0 := by
      have hprod := (mul_eq_zero.mp h.symm).resolve_right (hBD _ (hreflect z hz haz))
      exact (mul_eq_zero.mp hprod).resolve_left (mul_ne_zero c.ne_zero (zpow_ne_zero m hz))
    exact hDroots z hDz
  have hDconstant := constant_of_no_roots D hDroots
  have hEconstant := constant_of_no_roots E hEroots
  have hgc : g.coeff 0 ≠ 0 := by
    intro hzero
    have h := congrArg (fun A : ℂ[X] => A.coeff 0) hPfactor
    simp [mul_coeff_zero, hP0, hzero] at h
  have hDE0 : D.coeff 0 = E.coeff 0 := by
    apply mul_left_cancel₀ hgc
    calc
      g.coeff 0 * D.coeff 0 = 1 := by
        simpa only [mul_coeff_zero, hP0] using
          congrArg (fun A : ℂ[X] => A.coeff 0) hPfactor
      _ = g.coeff 0 * E.coeff 0 := by
        simpa only [mul_coeff_zero, hB0] using
          (congrArg (fun A : ℂ[X] => A.coeff 0) hBfactor).symm
  calc
    P = g * D := hPfactor.symm
    _ = g * E := by rw [hDconstant, hEconstant, hDE0]
    _ = B := hBfactor

/-- The corresponding quotient identity gives the same uniqueness conclusion.
Dual nonvanishing at zero justifies cross multiplication. -/
theorem gammaDecompositionUniqueness_of_ratio
    (a b : ℝ) (δ c : ℂˣ) (m : ℤ) (P PD B BD : ℂ[X])
    (ha : 0 < a) (hb : 0 < b) (hgap : ‖(δ : ℂ)‖ < a * b)
    (hP0 : P.coeff 0 = 1) (hB0 : B.coeff 0 = 1)
    (hP : ∀ z : ℂ, ‖z‖ < a → P.eval z ≠ 0)
    (hB : ∀ z : ℂ, ‖z‖ < a → B.eval z ≠ 0)
    (hPD : ∀ z : ℂ, ‖z‖ < b → PD.eval z ≠ 0)
    (hBD : ∀ z : ℂ, ‖z‖ < b → BD.eval z ≠ 0)
    (hratio : algebraMap ℂ[X] (RatFunc ℂ) B /
        RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) BD) =
      (RatFunc.C (c : ℂ) * (RatFunc.X : RatFunc ℂ) ^ m) *
        algebraMap ℂ[X] (RatFunc ℂ) P /
          RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) PD)) :
    P = B := by
  have hreflected (A : ℂ[X]) (hA : ∀ z : ℂ, ‖z‖ < b → A.eval z ≠ 0) :
      RationalReflection.subst δ (algebraMap ℂ[X] (RatFunc ℂ) A) ≠ 0 := by
    apply (map_ne_zero (RationalReflection.subst δ)).mpr
    intro hzero
    have hA0 : A.eval 0 ≠ 0 := hA 0 (by simpa using hb)
    have hAz : A = 0 := RatFunc.algebraMap_injective ℂ (by simpa using hzero)
    exact hA0 (by simp [hAz])
  exact gammaDecompositionUniqueness a b δ c m P PD B BD ha hb hgap
    hP0 hB0 hP hB hPD hBD
    ((div_eq_div_iff (hreflected BD hBD) (hreflected PD hPD)).mp hratio)

end Langlands.RankinSelberg
