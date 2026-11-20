import Langlands.Representation.Archimedean.ComplexGeneralLinearHaarDensity
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSingularNull
import Mathlib.RingTheory.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Determinant density for complex matrix Haar measures -/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.GodementJacquet

open RankinSelberg.GLDeterminantDensity

local instance matrixHaarGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℂ) := borel _
local instance matrixHaarGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℂ) := ⟨rfl⟩

/-- The complex normalized absolute value, with nonnegative values. -/
abbrev complexAbsHom : ℂ →*₀ ℝ≥0 := Langlands.Archimedean.ComplexGeneralLinearHaarDensity.normSqHom

@[simp]
theorem coe_complexAbsHom (z : ℂ) : (complexAbsHom z : ℝ) = ‖z‖ ^ 2 := rfl

theorem continuous_complexAbsHom : Continuous complexAbsHom :=
  Langlands.Archimedean.ComplexGeneralLinearHaarDensity.continuous_normSqHom

/-- Complex scalar multiplication scales the additive measure by the inverse
squared complex norm. -/
theorem map_complex_mul_volume {z : ℂ} (hz : z ≠ 0) :
    (volume : Measure ℂ).map (fun x => z * x) = (complexAbsHom z)⁻¹ • volume := by
  have hd : LinearMap.det (Algebra.lmul ℝ ℂ z) = Complex.normSq z :=
    (Algebra.norm_apply ℝ z).symm.trans (Algebra.norm_complex_apply z)
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ℂ))
    (f := Algebra.lmul ℝ ℂ z) (by rw [hd]; exact (Complex.normSq_pos.mpr hz).ne')
  rw [hd, Complex.normSq_eq_norm_sq, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))] at h
  change (volume : Measure ℂ).map (fun x => z * x) =
    (((complexAbsHom z)⁻¹ : ℝ≥0) : ℝ≥0∞) • volume
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, coe_complexAbsHom]
  exact h

/-- The same scalar change of variables for any additive Haar normalization. -/
theorem map_complex_mul_addHaar (μ : Measure ℂ) [μ.IsAddHaarMeasure] {z : ℂ} (hz : z ≠ 0) :
    μ.map (fun x => z * x) = (complexAbsHom z)⁻¹ • μ := by
  have h := Measure.isAddLeftInvariant_eq_smul μ (volume : Measure ℂ)
  rw [h, Measure.map_smul, map_complex_mul_volume hz, smul_comm]
  exact (continuous_const.mul continuous_id).measurable.aemeasurable

variable (n : ℕ)
local notation "G" => GeneralLinear n ℂ
local notation "M" => Matrix (Fin n) (Fin n) ℂ

/-- Left multiplication by an invertible matrix scales any additive Haar
measure by the inverse determinant weight. -/
theorem map_complex_matrix_left (μ : Measure M) [μ.IsAddHaarMeasure] (g : G) :
    μ.map (fun X => g.val * X) = weight n complexAbsHom g • μ := by
  have h := HarmonicAnalysis.haarMeasure_map_rectangular (volume : Measure ℂ) complexAbsHom
    (fun z hz => map_complex_mul_volume hz) μ g.val (1 : M)
    (Matrix.GeneralLinearGroup.det_ne_zero g) (by simp)
  simpa only [Matrix.mul_one, Matrix.det_one, map_one, one_pow, mul_one, Fintype.card_fin,
    weight_eq, inv_pow] using h

/-- Right multiplication has the same determinant scaling. -/
theorem map_complex_matrix_right (μ : Measure M) [μ.IsAddHaarMeasure] (g : G) :
    μ.map (fun X => X * g.val) = weight n complexAbsHom g • μ := by
  have h := HarmonicAnalysis.haarMeasure_map_rectangular (volume : Measure ℂ) complexAbsHom
    (fun z hz => map_complex_mul_volume hz) μ (1 : M) g.val
    (by simp) (Matrix.GeneralLinearGroup.det_ne_zero g)
  simpa only [Matrix.one_mul, Matrix.det_one, map_one, one_pow, one_mul, Fintype.card_fin,
    weight_eq, inv_pow] using h

/-- The corresponding Haar measure on the invertible matrices. Its density
relative to the pulled-back additive Haar measure is `|det|_ℂ⁻ⁿ`. -/
def complexMatrixHaar (μ : Measure M) : Measure G :=
  weightedRestriction n complexAbsHom μ

theorem complexMatrixHaar_isHaar (μ : Measure M) [μ.IsAddHaarMeasure] :
    (complexMatrixHaar n μ).IsHaarMeasure := by
  let : LocallyCompactSpace M := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  let : LocallyCompactSpace G :=
    (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).locallyCompactSpace
  exact weightedRestriction_isHaar n complexAbsHom continuous_complexAbsHom μ
    (map_complex_matrix_left n μ)

private theorem additiveRestriction_map_right (μ : Measure M) [μ.IsAddHaarMeasure] (g : G) :
    (additiveRestriction n μ).map (fun h => h * g) =
      weight n complexAbsHom g • additiveRestriction n μ := by
  have he := (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).measurableEmbedding
  have hm : Measurable (fun X : M => X * g.val) := (continuous_id.mul continuous_const).measurable
  have hg : Measurable (fun h : G => h * g) := (continuous_id.mul continuous_const).measurable
  have hpre (s : Set G) : Units.val '' ((fun h => h * g) ⁻¹' s) =
      (fun X => X * g.val) ⁻¹' (Units.val '' s) := by
    ext X
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨h * g, hh, rfl⟩
    · rintro ⟨h, hh, hx⟩
      refine ⟨h * g⁻¹, ?_, ?_⟩
      · change h * g⁻¹ * g ∈ s
        simpa only [inv_mul_cancel_right] using hh
      · change h.val * (g⁻¹).val = X
        rw [hx, Matrix.mul_assoc, show g.val * (g⁻¹).val = 1 from g.val_inv, Matrix.mul_one]
  ext s hs
  rw [Measure.map_apply hg hs, additiveRestriction, he.comap_apply, hpre,
    ← Measure.map_apply hm (he.measurableSet_image.mpr hs), map_complex_matrix_right]
  simp only [Measure.smul_apply, he.comap_apply]

/-- The determinant-weighted Haar measure is right invariant as well. -/
theorem complexMatrixHaar_isMulRightInvariant (μ : Measure M) [μ.IsAddHaarMeasure] :
    (complexMatrixHaar n μ).IsMulRightInvariant := by
  have hw : Measurable (fun h : G => (weight n complexAbsHom h : ℝ≥0∞)) :=
    (continuous_weight n complexAbsHom continuous_complexAbsHom).measurable.coe_nnreal_ennreal
  constructor
  intro g
  change (weightedRestriction n complexAbsHom μ).map (MeasurableEquiv.mulRight g) = _
  rw [weightedRestriction, map_withDensity_equiv]
  change ((additiveRestriction n μ).map (fun h => h * g)).withDensity
    (fun h => (weight n complexAbsHom (h * g⁻¹) : ℝ≥0∞)) = _
  rw [additiveRestriction_map_right]
  change ((weight n complexAbsHom g : ℝ≥0∞) • additiveRestriction n μ).withDensity
    (fun h => (weight n complexAbsHom (h * g⁻¹) : ℝ≥0∞)) = _
  rw [withDensity_smul_measure]
  simp only [weight_mul, weight_inv, ENNReal.coe_mul, ENNReal.coe_inv
    (weight_ne_zero n complexAbsHom g), mul_comm _ (↑(weight n complexAbsHom g) : ℝ≥0∞)⁻¹]
  rw [show (fun h : G => (weight n complexAbsHom g : ℝ≥0∞)⁻¹ *
      (weight n complexAbsHom h : ℝ≥0∞)) =
    ((weight n complexAbsHom g : ℝ≥0∞)⁻¹ •
      (fun h : G => (weight n complexAbsHom h : ℝ≥0∞))) by rfl,
    withDensity_smul _ hw, smul_smul]
  rw [ENNReal.mul_inv_cancel (by exact_mod_cast weight_ne_zero n complexAbsHom g)
    ENNReal.coe_ne_top, one_smul]
  rfl

theorem ae_complex_det_ne_zero (μ : Measure M) [μ.IsAddHaarMeasure] :
    ∀ᵐ X ∂μ, X.det ≠ 0 := by
  let : SigmaCompactSpace M := inferInstanceAs (SigmaCompactSpace (Fin n → Fin n → ℂ))
  let : SigmaFinite μ := SigmaFinite.of_isFiniteMeasureOnCompacts μ
  exact ae_det_ne_zero_of_addInvariant n (volume : Measure ℂ) μ

/-- The determinant density formula holds on the full additive matrix space
because the singular locus is null. -/
theorem complexMatrixHaar_map (μ : Measure M) [μ.IsAddHaarMeasure] :
    (complexMatrixHaar n μ).map Units.val =
      μ.withDensity (fun X => (matrixWeight n complexAbsHom X : ℝ≥0∞)) := by
  rw [complexMatrixHaar, weightedRestriction_map]
  congr 1
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [ae_complex_det_ne_zero n μ] with X hX
  exact (Matrix.isUnit_iff_isUnit_det X).mpr (isUnit_iff_ne_zero.mpr hX)

end Langlands.GodementJacquet
