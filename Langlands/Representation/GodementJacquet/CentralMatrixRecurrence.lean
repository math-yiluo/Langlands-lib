import Langlands.Representation.GodementJacquet.CentralScalingRecurrence
import Langlands.Representation.GodementJacquet.CentralCompactSupport
import Langlands.Representation.RankinSelberg.CharacterChange
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Central differences of actual matrix integrals -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis RankinSelberg Filter
open scoped Topology

universe uF

variable {F : Type uF} [Field F] [TopologicalSpace F]
  [IsTopologicalDivisionRing F] [T2Space F] {n : ℕ}

/-- Multiplication on the left by an invertible matrix, on the full matrix space. -/
def matrixLeftHomeomorph (z : Langlands.GeneralLinear (n + 1) F) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F ≃ₜ
      Matrix (Fin (n + 1)) (Fin (n + 1)) F where
  toFun x := z.val * x
  invFun x := (z⁻¹).val * x
  left_inv x := by
    change (z⁻¹).val * (z.val * x) = x
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  right_inv x := by
    change z.val * ((z⁻¹).val * x) = x
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

/-- A matrix test pulled back by multiplication with an invertible matrix. -/
def matrixTestLeftTranslate (z : Langlands.GeneralLinear (n + 1) F)
    (Φ : MatrixTestFunction n F) : MatrixTestFunction n F :=
  ⟨fun x => Φ (z.val * x),
    Φ.locallyConstant.comp_continuous (matrixLeftHomeomorph z).continuous,
    Φ.hasCompactSupport.comp_homeomorph (matrixLeftHomeomorph z)⟩

/-- The scalar finite difference used to remove the central tail at zero. -/
def matrixTestDifference (z : Langlands.GeneralLinear (n + 1) F)
    (Φ : MatrixTestFunction n F) : MatrixTestFunction n F :=
  Φ - matrixTestLeftTranslate z⁻¹ Φ

omit [T2Space F] in
@[simp] theorem matrixTestDifference_apply (z : Langlands.GeneralLinear (n + 1) F)
    (Φ : MatrixTestFunction n F) (x : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    matrixTestDifference z Φ x = Φ x - Φ ((z⁻¹).val * x) := rfl

omit [T2Space F] in
@[simp] theorem matrixTestDifference_zero (z : Langlands.GeneralLinear (n + 1) F)
    (Φ : MatrixTestFunction n F) : matrixTestDifference z Φ 0 = 0 := by
  simp

/-- Central compactness makes the finite-difference test times coefficient
compactly supported on the group. -/
theorem hasCompactSupport_matrixTestDifference_mul
    (z : Langlands.GeneralLinear (n + 1) F) (Φ : MatrixTestFunction n F)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (K : Set (Langlands.GeneralLinear (n + 1) F)) (hK : IsCompact K)
    (hf : Function.support f ⊆ scalarSaturation K) :
    HasCompactSupport (fun g => matrixTestDifference z Φ g.val * f g) :=
  hasCompactSupport_test_mul_of_scalarSaturation _ (matrixTestDifference_zero z Φ) f K hK hf

omit [T2Space F] in
/-- Each inverse orbit of a determinant contraction leaves the matrix test
support. Only compactness of the full matrix support is used. -/
theorem exists_matrixTest_inverse_mul_pow_eq_zero
    (abv : AbsoluteValue F ℝ) (habv : Continuous abv)
    (z : Langlands.GeneralLinear (n + 1) F) (hz : abv (Matrix.det z.val) < 1)
    (Φ : MatrixTestFunction n F) (g : Langlands.GeneralLinear (n + 1) F) :
    ∃ N : ℕ, Φ (((z⁻¹) ^ N * g).val) = 0 := by
  have hzpos : 0 < abv (Matrix.det z.val) := abv.pos z.det_ne_zero
  have hgpos : 0 < abv (Matrix.det g.val) := abv.pos g.det_ne_zero
  obtain ⟨M, hM⟩ := Φ.hasCompactSupport.exists_bound_of_continuousOn
    (habv.comp continuous_id.matrix_det).continuousOn
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
    (M / abv (Matrix.det g.val)) (one_lt_inv₀ hzpos |>.mpr hz)
  refine ⟨N, ?_⟩
  by_contra hn
  have hbound := hM _ (subset_tsupport _ hn)
  change ‖abv (Matrix.det (((z⁻¹) ^ N * g).val))‖ ≤ M at hbound
  have hdet : abv (Matrix.det (((z⁻¹) ^ N * g).val)) =
      (abv (Matrix.det z.val))⁻¹ ^ N * abv (Matrix.det g.val) := by
    change abv (GeneralLinear.determinant ((z⁻¹) ^ N * g) : F) = _
    rw [map_mul, map_pow, map_inv, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, map_mul, map_pow, map_inv₀]
    rfl
  rw [Real.norm_of_nonneg (abv.nonneg _), hdet] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hgpos).mp hN)

omit [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F] in
/-- One common right half-plane contracts the central ratio for all tests and
coefficients having the same central scalar. -/
theorem exists_halfPlane_norm_matrixRatio_lt_one
    (abv : AbsoluteValue F ℝ)
    (z : Langlands.GeneralLinear (n + 1) F) (hz : abv (Matrix.det z.val) < 1)
    (ω t : ℂ) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      ‖ω * determinantWeight abv z (s + t)‖ < 1 := by
  have hzpos : 0 < abv (Matrix.det z.val) := abv.pos z.det_ne_zero
  have htend : Tendsto (fun x : ℝ => ‖ω‖ * abv (Matrix.det z.val) ^ x) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_rpow_atTop_of_base_lt_one _ (by linarith) hz)
  obtain ⟨b, hb⟩ := eventually_atTop.mp (htend.eventually (Iio_mem_nhds zero_lt_one))
  refine ⟨b - t.re, fun s hs => ?_⟩
  rw [norm_mul, determinantWeight, Complex.norm_cpow_eq_rpow_re_of_pos hzpos]
  exact hb _ (by simpa only [Complex.add_re] using (show b ≤ s.re + t.re by linarith))

omit [T2Space F] in
/-- The actual matrix integrand difference equals the scalar recurrence
associated to central covariance of the coefficient. -/
theorem matrixIntegrand_difference
    (abv : AbsoluteValue F ℝ) (z : Langlands.GeneralLinear (n + 1) F)
    (ω : ℂ) (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hcov : ∀ g, f (z * g) = ω * f g) (Φ : MatrixTestFunction n F) (s : ℂ) :
    matrixIntegrand abv (matrixTestDifference z Φ) s f =
      geometricDifference (fun g => z⁻¹ * g) (ω * determinantWeight abv z s)
        (matrixIntegrand abv Φ s f) := by
  funext g
  have hf : f g = ω * f (z⁻¹ * g) := by simpa using hcov (z⁻¹ * g)
  have hw : determinantWeight abv g s = determinantWeight abv z s *
      determinantWeight abv (z⁻¹ * g) s := by
    simpa using determinantWeight_mul abv z (z⁻¹ * g) s
  simp only [matrixIntegrand, matrixTestDifference_apply, geometricDifference, Units.val_mul]
  rw [hf, hw]
  ring

variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]

omit [T2Space F] in
/-- For a determinant contraction, the integrable matrix finite difference
implies actual convergence and the geometric integral quotient. -/
theorem matrixIntegral_eq_div_of_difference
    (abv : AbsoluteValue F ℝ) (habv : Continuous abv)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F)) [IsMulLeftInvariant μ]
    (z : Langlands.GeneralLinear (n + 1) F) (hz : abv (Matrix.det z.val) < 1)
    (ω : ℂ) (f : Langlands.GeneralLinear (n + 1) F → ℂ) (hf : Continuous f)
    (hcov : ∀ g, f (z * g) = ω * f g)
    (Φ : MatrixTestFunction n F) (s : ℂ)
    (hr : ‖ω * determinantWeight abv z s‖ < 1)
    (hD : MatrixConverges abv μ (matrixTestDifference z Φ) s f) :
    MatrixConverges abv μ Φ s f ∧
      matrixIntegral abv μ Φ s f =
        matrixIntegral abv μ (matrixTestDifference z Φ) s f /
          (1 - ω * determinantWeight abv z s) := by
  have hw : Continuous (fun g : Langlands.GeneralLinear (n + 1) F =>
      determinantWeight abv g s) := by
    apply (Complex.continuous_ofReal.comp
      (habv.comp Units.continuous_val.matrix_det)).cpow continuous_const
    intro g
    exact Complex.ofReal_mem_slitPlane.mpr (abv.pos (Matrix.GeneralLinearGroup.det_ne_zero g))
  have hH : Measurable (matrixIntegrand abv Φ s f) :=
    (((Φ.continuous.comp Units.continuous_val).mul hf).mul hw).measurable
  have hzero : ∀ g, ∃ N : ℕ,
      matrixIntegrand abv Φ s f ((fun g => z⁻¹ * g)^[N] g) = 0 := by
    intro g
    obtain ⟨N, hN⟩ := exists_matrixTest_inverse_mul_pow_eq_zero abv habv z hz Φ g
    refine ⟨N, ?_⟩
    simp only [mul_left_iterate_apply, matrixIntegrand, hN, zero_mul]
  rw [MatrixConverges, matrixIntegrand_difference abv z ω f hcov Φ s] at hD
  have hresult := integral_eq_div_of_geometricDifference μ (MeasurableEquiv.mulLeft z⁻¹)
    (measurePreserving_mul_left μ z⁻¹) (ω * determinantWeight abv z s) hr
    (matrixIntegrand abv Φ s f) hH hD hzero
  change Integrable (matrixIntegrand abv Φ s f) μ ∧
    (∫ g, matrixIntegrand abv Φ s f g ∂μ) =
      (∫ g, matrixIntegrand abv (matrixTestDifference z Φ) s f g ∂μ) /
        (1 - ω * determinantWeight abv z s)
  rw [matrixIntegrand_difference abv z ω f hcov Φ s]
  exact hresult

end Langlands.GodementJacquet
