import Langlands.Global.RankinSelberg.ComplexGapTailObservation
import Langlands.Global.RankinSelberg.ComplexStandardGaussianFourier
import Langlands.Analysis.GaussianWeightedMoment
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Nonzero retained integrals from polynomial Gaussian tail tests -/

noncomputable section

open Filter MeasureTheory MvPolynomial Set
open scoped Topology NNReal ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapRetained

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (rankInclusion)
open Langlands.Analysis.GaussianWeightedMoment (integral_eq_zero_of_gaussian_moments)
open ComplexGapLeadingHaar (retainedMeasure)
open ComplexTraceFourier (realCoordinates standardGaussian)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel

variable (t q : ℕ)
local notation "Rank" => t + 1 + q + 1
local notation "Ids" => Fin (q + 2)
local notation "Vec" => Fin Rank → ℂ
local notation "Obs" => Ids → Vec
local notation "P" => RetainedPoint t q
local notation "Idx" => Fin Rank × Bool
local notation "E" => ComplexTraceFourier.Coordinates (Ids × Fin Rank)
local notation "c₀" => (2 * Real.pi : ℝ)

private theorem radius_pos : 0 < Real.sqrt c₀ := Real.sqrt_pos.mpr (by positivity)

private def pack : Obs →ₗ[ℝ] E where
  toFun v := Real.sqrt c₀ • (ComplexTraceFourier.coordinates (ι := Ids × Fin Rank)).symm (fun j => v j.1 j.2)
  map_add' v w := by
    have h : (fun j : Ids × Fin Rank => (v + w) j.1 j.2) =
        (fun j : Ids × Fin Rank => v j.1 j.2) + (fun j => w j.1 j.2) := rfl
    rw [h, map_add, smul_add]
  map_smul' r v := by
    have h : (fun j : Ids × Fin Rank => (r • v) j.1 j.2) = r • (fun j : Ids × Fin Rank => v j.1 j.2) := rfl
    rw [h, map_smul, RingHom.id_apply, smul_comm]

private theorem continuous_pack : Continuous (pack t q) := (pack t q).continuous_of_finiteDimensional

private def unpack (z : E) : Obs := fun j i => (Real.sqrt c₀)⁻¹ • z (j, i)

private theorem continuous_unpack : Continuous (unpack t q) := by
  apply continuous_pi fun j => continuous_pi fun i => ?_
  exact (PiLp.continuous_apply 2 (fun _ : Ids × Fin Rank => ℂ) (j, i)).const_smul ((Real.sqrt c₀)⁻¹ : ℝ)

private theorem unpack_pack (v : Obs) : unpack t q (pack t q v) = v := by
  funext j i
  change (Real.sqrt c₀)⁻¹ • (Real.sqrt c₀ • v j i) = v j i
  rw [smul_smul, inv_mul_cancel₀ radius_pos.ne', one_smul]

private theorem pack_norm (v : Obs) : ‖pack t q v‖ ^ 2 = c₀ * ∑ j, ∑ i, ‖v j i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ j : Ids × Fin Rank, ‖(Real.sqrt c₀) • v j.1 j.2‖ ^ 2) = _
  simp only [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity : 0 ≤ c₀),
    Finset.mul_sum, Fintype.sum_prod_type]

/-- The Gaussian weight of half the standard exponent, in observation coordinates. -/
def halfTailGaussian (p : P) : ℂ :=
  (Real.exp (-c₀ * (∑ j, ∑ i, ‖tailObservation t q p j i‖ ^ 2) / 2) : ℂ)

/-- The product of standard polynomial Gaussian tests on the observed columns. -/
def tailGaussianProduct (Q : Ids → MvPolynomial Idx ℂ) (v : Obs) : ℂ :=
  ∏ j, standardGaussian (Q j) (v j)

private def obsCoordinates (v : Obs) (j : Ids × Idx) : ℂ := realCoordinates (v j.1) j.2

private def coordinateVector (j : Ids × Idx) : Obs :=
  Pi.single j.1 (Pi.single j.2.1 (if j.2.2 then Complex.I else 1))

private theorem obs_coordinate_sum (v : Obs) :
    (∑ j : Ids × Idx, (obsCoordinates t q v j).re • coordinateVector t q j) = v := by
  classical
  funext j i
  simp only [Fintype.sum_prod_type, Finset.sum_apply, Pi.smul_apply, coordinateVector]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · rw [Fintype.sum_bool]
      simp only [Pi.single_eq_same, ite_true, Bool.false_eq_true, ite_false, obsCoordinates, realCoordinates, Complex.ofReal_re]
      apply Complex.ext <;> simp [Complex.real_smul, Complex.mul_re, Complex.mul_im]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

private theorem exists_directionPolynomial (L : E →L[ℝ] ℝ) :
    ∃ Q : MvPolynomial (Ids × Idx) ℂ, ∀ v : Obs, eval (obsCoordinates t q v) Q = (L (pack t q v) : ℂ) := by
  let Q := ∑ j : Ids × Idx, C (L (pack t q (coordinateVector t q j)) : ℂ) * X j
  refine ⟨Q, fun v => ?_⟩
  have h := congrArg (fun x : Obs => (L (pack t q x) : ℂ)) (obs_coordinate_sum t q v)
  rw [← h]
  simp only [Q, map_sum, map_mul, eval_C, eval_X, map_smul, smul_eq_mul, Complex.ofReal_sum,
    Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have he : ((obsCoordinates t q v j).re : ℂ) = obsCoordinates t q v j := by
    rcases j with ⟨j, i, b⟩
    cases b <;> simp [obsCoordinates, realCoordinates]
  rw [he, mul_comm]

private theorem gaussian_monomial_product (b : (Ids × Idx) →₀ ℕ) (c : ℂ) (v : Obs) :
    eval (obsCoordinates t q v) (monomial b c) * (Real.exp (-‖pack t q v‖ ^ 2) : ℂ) =
      c * tailGaussianProduct t q (fun j => monomial (Finsupp.equivFunOnFinite.symm (fun i => b (j, i))) 1) v := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun z => pow_zero (obsCoordinates t q v z)), pack_norm]
  unfold tailGaussianProduct standardGaussian
  have hf (j : Ids) : eval (realCoordinates (v j)) (monomial (Finsupp.equivFunOnFinite.symm (fun i : Idx => b (j, i))) 1) =
      ∏ i : Idx, obsCoordinates t q v (j, i) ^ b (j, i) := by
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun z => pow_zero (realCoordinates (v j) z)), one_mul]
    rfl
  simp only [hf, Finset.prod_mul_distrib, Fintype.prod_prod_type, mul_assoc]
  congr 2
  rw [← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum]
  congr 2
  ring

private theorem gaussian_moments_vanish {η : Measure P} (F : P → ℂ)
    (hInt : ∀ Q : Ids → MvPolynomial Idx ℂ, Integrable (fun p => tailGaussianProduct t q Q (tailObservation t q p) * F p) η)
    (hZ : ∀ Q : Ids → MvPolynomial Idx ℂ, (∫ p, tailGaussianProduct t q Q (tailObservation t q p) * F p ∂η) = 0)
    (L : E →L[ℝ] ℝ) (l : ℕ) :
    (∫ p, (L (pack t q (tailObservation t q p)) : ℂ) ^ l *
      ((Real.exp (-‖pack t q (tailObservation t q p)‖ ^ 2) : ℂ) * F p) ∂η) = 0 := by
  obtain ⟨Q, hQ⟩ := exists_directionPolynomial t q L
  let A := Q ^ l
  let v := tailObservation t q
  let M₀ (b : (Ids × Idx) →₀ ℕ) (j : Ids) : MvPolynomial Idx ℂ := monomial (Finsupp.equivFunOnFinite.symm (fun i => b (j, i))) 1
  have he (p : P) : (L (pack t q (v p)) : ℂ) ^ l * ((Real.exp (-‖pack t q (v p)‖ ^ 2) : ℂ) * F p) =
      ∑ b ∈ A.support, A.coeff b * (tailGaussianProduct t q (M₀ b) (v p) * F p) := by
    rw [← hQ, ← map_pow, ← mul_assoc]
    change eval (obsCoordinates t q (v p)) A * (Real.exp (-‖pack t q (v p)‖ ^ 2) : ℂ) * F p = _
    have hsum : eval (obsCoordinates t q (v p)) A =
        ∑ b ∈ A.support, eval (obsCoordinates t q (v p)) (monomial b (A.coeff b)) := by
      exact (congrArg (eval (obsCoordinates t q (v p))) A.as_sum).trans (map_sum _ _ _)
    rw [hsum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [gaussian_monomial_product, mul_assoc]
  have hi (b) (_ : b ∈ A.support) : Integrable (fun p => A.coeff b * (tailGaussianProduct t q (M₀ b) (v p) * F p)) η :=
    (hInt _).const_mul _
  change (∫ p, (L (pack t q (v p)) : ℂ) ^ l * ((Real.exp (-‖pack t q (v p)‖ ^ 2) : ℂ) * F p) ∂η) = 0
  simp_rw [he]
  rw [integral_finsetSum _ hi]
  simp only [integral_const_mul, v, hZ, mul_zero, Finset.sum_const_zero]

/-- A continuous retained coefficient that is nonzero and constant on embedded leading
unitaries has a nonzero pairing with a product of standard polynomial Gaussians, provided
the half-strength Gaussian and the standard polynomial products are integrable. -/
def ComplexGapTailMomentsStatement : Prop :=
  ∀ (η : Measure P) [Measure.IsOpenPosMeasure η] (F : P → ℂ), Continuous F →
    ∀ b : ℂ, b ≠ 0 →
    (∀ p : P, (∃ u : unitaryCompact ℂ (t + 1), retainedGroup t q p = rankInclusion (q + 1) u.val) → F p = b) →
    Integrable (fun p => halfTailGaussian t q p * F p) η →
    (∀ Q : Ids → MvPolynomial Idx ℂ, Integrable (fun p => tailGaussianProduct t q Q (tailObservation t q p) * F p) η) →
    ∃ Q : Ids → MvPolynomial Idx ℂ, (∫ p, tailGaussianProduct t q Q (tailObservation t q p) * F p ∂η) ≠ 0

set_option maxHeartbeats 1800000 in
theorem complexGapTailMoments : ComplexGapTailMomentsStatement t q := by
  intro η _ F hF b hb hCenter hThin hInt
  by_contra! hGone
  let O := pack t q ∘ tailObservation t q
  have hO : Continuous O := (continuous_pack t q).comp (continuous_tailObservation t q)
  have hThin' : Integrable (fun p => (Real.exp (-‖O p‖ ^ 2 / 2) : ℂ) * F p) η := by
    simpa only [O, Function.comp_apply, pack_norm, halfTailGaussian, neg_mul] using hThin
  let R (p : P) := (star b * F p).re
  have hR : Continuous R := Complex.continuous_re.comp (hF.const_mul _)
  let S := {p | 0 < R p}
  have hS : IsOpen S := isOpen_lt continuous_const hR
  have hb' : 0 < (star b * b).re := by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    exact pow_pos (norm_pos_iff.mpr hb) _
  obtain ⟨V, hV, hStd, hPre⟩ := exists_tailObservation_neighborhood t q S hS (fun p hp => by
    change 0 < (star b * F p).re
    rw [hCenter p hp]
    exact hb')
  let z := pack t q (standardTailObservation t q)
  let V' := unpack t q ⁻¹' V
  have hV' : IsOpen V' := hV.preimage (continuous_unpack t q)
  have hz : z ∈ V' := by simpa only [V', z, mem_preimage, unpack_pack] using hStd
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV' z hz
  let g₀ (x : E) := max 0 (r - dist x z)
  let g (x : E) : ℂ := (g₀ x * Real.exp (-‖x‖ ^ 2 / 2) : ℝ)
  have hg₀ : Continuous g₀ := continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hg : Continuous g := Complex.continuous_ofReal.comp (hg₀.mul (by fun_prop))
  have hI : Integrable (fun p => g (O p) * F p) η := by
    refine (hThin'.norm.const_mul r).mono' ((hg.comp hO).mul hF).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    have hle : g₀ (O p) ≤ r := max_le hr.le (sub_le_self _ dist_nonneg)
    have h₀ : 0 ≤ g₀ (O p) := le_max_left _ _
    simp only [g, Complex.ofReal_mul, mul_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg h₀]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hzI := integral_eq_zero_of_gaussian_moments hO.measurable hF.measurable hThin'
    (gaussian_moments_vanish t q F hInt hGone) hg.measurable hI
  let G (p : P) := (star b * (g (O p) * F p)).re
  have hGc : Continuous G := Complex.continuous_re.comp (((hg.comp hO).mul hF).const_mul _)
  have hGi : Integrable G η := (hI.const_mul _).re
  have hGe (p : P) : G p = g₀ (O p) * Real.exp (-‖O p‖ ^ 2 / 2) * R p := by
    change (star b * ((↑(g₀ (O p) * Real.exp (-‖O p‖ ^ 2 / 2)) : ℂ) * F p)).re = _
    rw [mul_left_comm, Complex.re_ofReal_mul]
  have hG₀ : 0 ≤ G := by
    intro p
    change 0 ≤ G p
    rw [hGe]
    by_cases hp : O p ∈ Metric.ball z r
    · have hpos : 0 < R p := hPre (by simpa only [V', O, mem_preimage, Function.comp_apply, unpack_pack] using hball hp)
      exact mul_nonneg (mul_nonneg (le_max_left _ _) (Real.exp_nonneg _)) hpos.le
    · have hle : r ≤ dist (O p) z := le_of_not_gt hp
      simp only [g₀, max_eq_left (sub_nonpos.mpr hle), zero_mul, le_rfl]
  obtain ⟨p₀, hp₀⟩ := standardTailObservation_mem_range t q
  have hO₀ : O p₀ = z := congrArg (pack t q) hp₀
  have hRp₀ : 0 < R p₀ := hPre (show tailObservation t q p₀ ∈ V by rw [hp₀]; exact hStd)
  have hGp₀ : 0 < G p₀ := by
    rw [hGe, hO₀]
    exact mul_pos (mul_pos (by simp [g₀, hr]) (Real.exp_pos _)) hRp₀
  have hSupp : IsOpen (Function.support G) := hGc.isOpen_support
  have hNonempty : (Function.support G).Nonempty := ⟨p₀, hGp₀.ne'⟩
  have hPos : 0 < ∫ p, G p ∂η := (integral_pos_iff_support_of_nonneg hG₀ hGi).mpr (hSupp.measure_pos η hNonempty)
  have hZero : (∫ p, G p ∂η) = 0 := by
    change (∫ p, (star b * (g (O p) * F p)).re ∂η) = _
    have he := integral_re (hI.const_mul (star b))
    change (∫ p, (star b * (g (O p) * F p)).re ∂η) = (∫ p, star b * (g (O p) * F p) ∂η).re at he
    rw [integral_const_mul, hzI, mul_zero, Complex.zero_re] at he
    exact he
  exact hPos.ne' hZero

end Langlands.Global.RankinSelbergGlobal.ComplexGapRetained
