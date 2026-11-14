import Langlands.Representation.GodementJacquet.WhittakerMatrixConvergence
import Langlands.AllField.Representation.GodementJacquet.WhittakerMatrixRationality
import Langlands.AllField.Representation.GodementJacquet.WhittakerSliceBound
/-!
# Convergence of full-matrix Whittaker integrals

Given `FiniteFunctionMellinStatement`, for `W` as in `IsWhittakerLike` and a
full-matrix test function `Φ`, the integral `∫ Φ(g) W(g) |det g|^s dg` converges
absolutely on a right half-plane. The proof uses Iwasawa integration, the finite
coset sum over `K`, the unipotent volume bound, and the torus Mellin integrals.
See the paired Markdown.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement FiniteFunctionMellinStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable unequalRankIwasawaSupport unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators ENNReal

universe uF

namespace Padic
open Langlands.GodementJacquet.WhittakerTorus.Padic hiding HasTorusExpansion IsWhittakerLike borelModulus borelModulus_mul borelModulus_pos boxTest boxTest_apply_of_le continuous_borelModulus continuous_normalizedAbs_prod continuous_torusWeight enorm_torusWeight exists_slice_bound initTail integralK integral_iwasawa integral_unipotent_matrixIntegrand isClopen_normBox isCompact_normBox isFiniteFunction_torusWeight isFiniteFunction_twistedCharacter iwasawaReductionBorelSpace iwasawaReductionLocalField iwasawaReductionMeasurableSpace iwasawaReductionTopology iwasawaReductionUnipotentBorelSpace iwasawaReductionUnipotentMeasurableSpace iwasawaReductionUnitsBorelSpace iwasawaReductionUnitsMeasurableSpace iwasawaReductionValuativeRel lintegral_iwasawa lintegral_torus_lt_top lintegral_unipotent_matrixIntegrand matrixConvergenceBorelSpace matrixConvergenceLocalField matrixConvergenceMeasurableSpace matrixConvergenceTopology matrixConvergenceUnipotentBorelSpace matrixConvergenceUnipotentMeasurableSpace matrixConvergenceUnitsBorelSpace matrixConvergenceUnitsMeasurableSpace matrixConvergenceValuativeRel matrixIntegrand_iwasawa matrixIntegrand_mul_right matrixRationalityBorelSpace matrixRationalityLocalField matrixRationalityMeasurableSpace matrixRationalityTopology matrixRationalityUnipotentBorelSpace matrixRationalityUnipotentMeasurableSpace matrixRationalityUnitsBorelSpace matrixRationalityUnitsMeasurableSpace matrixRationalityValuativeRel measurable_matrixIntegrand normBox normalizedAbs_det_integralK normalizedAbs_prod_mul normalizedAbs_prod_pos normalizedAbs_units_pos ratios sliceBoundBorelSpace sliceBoundLocalField sliceBoundMeasurableSpace sliceBoundTopology sliceBoundUnipotentBorelSpace sliceBoundUnipotentMeasurableSpace sliceBoundValuativeRel sliceTest sliceTest_apply torusIntegrand torusIntegrand_tailProd torusMellin torusMellinLocalField torusMellinTopology torusMellinUnitsBorelSpace torusMellinUnitsMeasurableSpace torusMellinValuativeRel torusMonomial torusMonomial_nonneg torusWeight torusWeight_mul twistedCharacter
open Langlands.AllField.GodementJacquet.WhittakerTorus.Padic
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance matrixConvergenceUnitsMeasurableSpace : MeasurableSpace Fˣ := borel _
local instance matrixConvergenceUnitsBorelSpace : BorelSpace Fˣ := ⟨rfl⟩
local instance matrixConvergenceMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance matrixConvergenceBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance matrixConvergenceUnipotentMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance matrixConvergenceUnipotentBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

variable {n : ℕ}

/-! ### The torus weight `δ(a)⁻¹ ∏ |a_i|^(-e_i)` -/

/-- The weight `δ(a)⁻¹ ∏ |a_i|^(-e_i)` as a complex function on the torus. -/
def torusWeight (e : Fin (n + 1) → ℕ) (a : Fin (n + 1) → Fˣ) : ℂ :=
  (((borelModulus F a)⁻¹ * torusMonomial F e a : ℝ) : ℂ)

theorem torusWeight_mul (e : Fin (n + 1) → ℕ) (a b : Fin (n + 1) → Fˣ) :
    torusWeight F e (a * b) = torusWeight F e a * torusWeight F e b := by
  simp only [torusWeight, torusMonomial, borelModulus_mul, Pi.mul_apply, Units.val_mul,
    (⟨⟩ : LocalFieldData F).normalizedAbs_mul, mul_inv, mul_pow, Finset.prod_mul_distrib]
  push_cast
  ring

theorem continuous_torusWeight (e : Fin (n + 1) → ℕ) : Continuous (torusWeight F e) := by
  refine Complex.continuous_ofReal.comp (((continuous_borelModulus F).inv₀
    fun a => (borelModulus_pos F a).ne').mul ?_)
  refine continuous_finsetProd _ fun i _ => Continuous.pow ?_ _
  exact ((⟨⟩ : LocalFieldData F).continuous_normalizedAbs.comp
    (Units.continuous_val.comp (continuous_apply i))).inv₀
      fun a => ((⟨⟩ : LocalFieldData F).normalizedAbs_pos (a i).ne_zero).ne'

theorem isFiniteFunction_torusWeight (e : Fin (n + 1) → ℕ) :
    IsFiniteFunction (torusWeight F e) :=
  IsFiniteFunction.of_mul_apply (continuous_torusWeight F e) (torusWeight F e)
    fun b a => torusWeight_mul F e b a

theorem enorm_torusWeight (e : Fin (n + 1) → ℕ) (a : Fin (n + 1) → Fˣ) :
    ‖torusWeight F e a‖ₑ =
      ENNReal.ofReal ((borelModulus F a)⁻¹) * ENNReal.ofReal (torusMonomial F e a) := by
  have hδ : 0 ≤ (borelModulus F a)⁻¹ := (inv_pos.2 (borelModulus_pos F a)).le
  rw [torusWeight, ← ofReal_norm,
    Complex.norm_of_nonneg (mul_nonneg hδ (torusMonomial_nonneg F e a)),
    ENNReal.ofReal_mul hδ]

/-! ### Convergence -/

/-- For `k ∈ K`, the torus integral of the unipotent integral of the matrix
integrand at `u diag(a) k` is finite on a right half-plane. -/
theorem lintegral_torus_lt_top (hFFM : FiniteFunctionMellinStatement.{uF})
    {ψ : UnitaryAdditiveCharacter F}
    {W : Langlands.GeneralLinear (n + 1) F → ℂ} (hW : IsWhittakerLike F ψ W)
    (Φ : MatrixTestFunction n F) {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ integralK F n) :
    ∃ c : ℝ, ∀ s : ℂ, c < s.re →
      ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F n
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F) < ⊤ := by
  obtain ⟨B, ρ, hρ, e, hslice⟩ := exists_slice_bound F Φ k
  obtain ⟨X, hX, φ, hφ⟩ := hW.expansion k
  let J := boxTest F n hρ
  obtain ⟨c, hc⟩ := exists_common_halfPlane X
    (fun χ s => Integrable (torusIntegrand F (φ χ) J (χ * torusWeight F e) s)
      (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F))
    fun χ hχ => (torusMellin F hFFM _ ((hX χ hχ).mul (isFiniteFunction_torusWeight F e))
      (φ χ) J).1
  refine ⟨c, fun s hs => ?_⟩
  have hint := hc s hs
  have hpt : ∀ a : Fin (n + 1) → Fˣ,
      ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F n ≤
        ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
    intro a
    rw [lintegral_unipotent_matrixIntegrand F hW.equivariant Φ s a hk]
    have hsum : W (Iwasawa.diagonalUnits a * k) *
        (J (fun i => (a i : F)) * torusWeight F e a *
          (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ s) =
        ∑ χ ∈ X, torusIntegrand F (φ χ) J (χ * torusWeight F e) s a := by
      rw [show W (Iwasawa.diagonalUnits a * k) = ∑ χ ∈ X, φ χ (ratios F a) * χ a from hφ a,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun χ _ => ?_
      simp only [torusIntegrand, Pi.mul_apply]
      ring
    calc ENNReal.ofReal ((borelModulus F a)⁻¹) *
          (‖W (Iwasawa.diagonalUnits a * k) *
            (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ s‖ₑ *
          ∫⁻ u, ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val)‖ₑ
            ∂unipotentHaar F n)
        ≤ ENNReal.ofReal ((borelModulus F a)⁻¹) *
          (‖W (Iwasawa.diagonalUnits a * k) *
            (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ s‖ₑ *
          (ENNReal.ofReal B * ENNReal.ofReal (torusMonomial F e a) *
            ‖J (fun i => (a i : F))‖ₑ)) := by
          gcongr
          exact hslice a
      _ = ENNReal.ofReal B * ‖W (Iwasawa.diagonalUnits a * k) *
          (J (fun i => (a i : F)) * torusWeight F e a *
            (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^
              s)‖ₑ := by
          simp only [enorm_mul]
          rw [enorm_torusWeight]
          ring
      _ = ENNReal.ofReal B *
          ‖∑ χ ∈ X, torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
          rw [hsum]
      _ ≤ ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ := by
          gcongr
          exact enorm_sum_le _ _
  calc ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
          ∫⁻ u, ‖Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W
            (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F n
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F)
      ≤ ∫⁻ a, ENNReal.ofReal B *
          ∑ χ ∈ X, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal B * ∑ χ ∈ X, ∫⁻ a, ‖torusIntegrand F (φ χ) J (χ * torusWeight F e) s a‖ₑ
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun χ hχ => (hint χ hχ).aestronglyMeasurable.enorm]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun χ hχ =>
        hasFiniteIntegral_iff_enorm.1 (hint χ hχ).hasFiniteIntegral)

/-- **Convergence of full-matrix Whittaker integrals.** Given
`FiniteFunctionMellinStatement`, for `W` as in `IsWhittakerLike` and a
full-matrix test function `Φ`, the unshifted matrix integral
`∫ Φ(g) W(g) |det g|^s dg` converges absolutely for `Re s` large. -/
theorem IsWhittakerLike.matrixConverges (hFFM : FiniteFunctionMellinStatement.{uF})
    {ψ : UnitaryAdditiveCharacter F}
    {W : Langlands.GeneralLinear (n + 1) F → ℂ} (hW : IsWhittakerLike F ψ W)
    (Φ : MatrixTestFunction n F) :
    ∃ c : ℝ, ∀ s : ℂ, c < s.re → Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ s W := by
  obtain ⟨K₀, S, hK₀K, hSK, hinv, hlin, -⟩ := Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.IsWhittakerLike.exists_cosetSum F hW Φ
  obtain ⟨c, hc⟩ := exists_common_halfPlane S
    (fun k s => ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
        ∫⁻ u, ‖Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W
          (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F n
      ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F) < ⊤)
    fun k hk => lintegral_torus_lt_top F hFFM hW Φ (hSK hk)
  refine ⟨c, fun s hs => ?_⟩
  have hmeas := measurable_matrixIntegrand F hW.continuous Φ s
  change Integrable (Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W) (generalLinearHaar F n)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_iwasawa F _ hmeas.enorm,
    hlin (fun k => ∫⁻ a, ENNReal.ofReal ((borelModulus F a)⁻¹) *
        ∫⁻ u, ‖Langlands.AllField.GodementJacquet.Padic.matrixIntegrand F Φ s W
          (u.val * Iwasawa.diagonalUnits a * k)‖ₑ ∂unipotentHaar F n
      ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F))
      fun k _ k₀ hk₀ => ?_]
  · refine ENNReal.sum_lt_top.2 fun k hk => ENNReal.mul_lt_top ?_ (hc s hs k hk)
    exact (measure_mono fun x hx => hK₀K hx).trans_lt
      ((generalLinearHaar_integralSubgroup F n).trans_lt ENNReal.one_lt_top)
  · refine lintegral_congr fun a => ?_
    congr 1
    refine lintegral_congr fun u => ?_
    rw [← mul_assoc, hinv s _ k₀ hk₀]

end Padic

end Langlands.AllField.GodementJacquet.WhittakerTorus
