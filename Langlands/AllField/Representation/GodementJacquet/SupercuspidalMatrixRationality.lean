import Langlands.Representation.GodementJacquet.SupercuspidalMatrixRationality
import Langlands.AllField.Representation.GodementJacquet.CentralMatrixRationality
import Langlands.AllField.Representation.GodementJacquet.SupercuspidalMatrixSupport
import Langlands.AllField.Representation.GodementJacquet.TwoBlockAnalyticReversal
/-! # Common convergence and rationality for supercuspidal matrix coefficients -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding determinantNorm_ker_sup_center_finiteIndex exists_centralCharacter_compactScalarSupport hasCompactSupport_determinantUnit_coefficient inverseTransposeProductReversalEquiv iotaMatrixAnalyticAssertions_product_iff oneBlockDeterminantUnitHomeomorph
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF uV

section IotaSupport


end IotaSupport

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData SupercuspidalMatrixRationalityData centralMatrixRationalityBorelSpace centralMatrixRationalityLocalField centralMatrixRationalityMeasurableSpace centralMatrixRationalityT2Space centralMatrixRationalityTopology centralMatrixRationalityValuativeRel compactMatrixLaurentBorelSpace compactMatrixLaurentLocalField compactMatrixLaurentMeasurableSpace compactMatrixLaurentTopology compactMatrixLaurentValuativeRel determinantWeight_shift_spectral exists_laurent_integral_of_hasCompactSupport exists_laurent_matrixIntegral_of_hasCompactSupport exists_laurent_matrixIntegral_quotient exists_shiftedRationalValue_of_scalarSaturation exists_supercuspidalMatrixRationalityData instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixAnalyticAssertions_succBlocks_iff iotaMatrixRationalValues jpssI2 jpssI3 laurentEval_matrixGeometricDenominator matrixAnalyticAssertions_reversedInverseTransposeBlocks matrixGeometricDenominator matrixGeometricDenominator_ne_zero matrixIntegral matrixIntegrand matrixRationalValues matrixUniformizer matrixUniformizer_det_abs_lt_one supercuspidalMatrixRationalityBorelSpace supercuspidalMatrixRationalityLocalField supercuspidalMatrixRationalityMeasurableSpace supercuspidalMatrixRationalityTopology supercuspidalMatrixRationalityValuativeRel twoBlockReversalGLBorel twoBlockReversalGLMeasurable twoBlockReversalLocalField twoBlockReversalTopology twoBlockReversalValuation whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData determinantNorm_ker_sup_center_finiteIndex exists_centralCharacter_compactScalarSupport hasCompactSupport_determinantUnit_coefficient inverseTransposeProductReversalEquiv iotaMatrixAnalyticAssertions_product_iff iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues oneBlockDeterminantUnitHomeomorph whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance supercuspidalMatrixRationalityMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance supercuspidalMatrixRationalityBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

/-- The scalar matrix of the specified uniformizer, with its centrality proof. -/
def matrixUniformizer (n : ℕ) :
    Subgroup.center (Langlands.GeneralLinear (n + 1) F) :=
  GeneralLinear.scalarToCenter
    (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))

theorem matrixUniformizer_det_abs_lt_one (n : ℕ) :
    normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
      (Matrix.det (matrixUniformizer F n).val.val) < 1 := by
  have hd : Matrix.det (matrixUniformizer F n).val.val =
      ((Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F) :
        Fˣ) : F) ^ (n + 1) := by
    change ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar
      (Fin (n + 1)) (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
        (⟨⟩ : LocalFieldData F)))) : F) = _
    simp
  rw [hd, map_pow, normalizedAbsoluteValue_apply,
    Langlands.LocalFactor.LocalAbelian.uniformizerUnit_coe,
    (⟨⟩ : LocalFieldData F).normalizedAbs_uniformizer, zpow_neg_one]
  have hq : (1 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  exact pow_lt_one₀ (inv_nonneg.mpr (by positivity))
    ((inv_lt_one₀ (by positivity)).mpr hq) (Nat.succ_ne_zero n)

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Common convergence and actual rational values with one geometric
denominator for each of the two coefficient families. -/
def SupercuspidalMatrixRationalityData
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (ω : ℂˣ) : Prop :=
  MatrixConvergesOnRight F ρ ∧ IotaMatrixConvergesOnRight F ρ ∧
    (∀ Φ : MatrixTestFunction n F, ∀ f : biSmoothMatrixCoefficients ρ,
      ∃ R : RationalFunctions,
        HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          (generalLinearHaar F n) Φ f.val R ∧
        ∃ A : LaurentCoefficients, laurentToRatFunc A =
          laurentToRatFunc (matrixGeometricDenominator F (matrixUniformizer F n).val ω) * R) ∧
    (∀ Φ : MatrixTestFunction n F, ∀ f : biSmoothMatrixCoefficients ρ,
      ∃ R : RationalFunctions,
        HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          (generalLinearHaar F n) Φ (coefficientIota f.val) R ∧
        ∃ A : LaurentCoefficients, laurentToRatFunc A =
          laurentToRatFunc
            (matrixGeometricDenominator F (matrixUniformizer F n).val (ω⁻¹ : ℂˣ)) * R)

/-- The compact scalar-support and Schur consequences of actual
supercuspidality imply both canonical common half-planes and rational families. -/
theorem exists_supercuspidalMatrixRationalityData
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible) :
    ∃ ω : ℂˣ, SupercuspidalMatrixRationalityData F ρ ω := by
  obtain ⟨χ, _, hf⟩ :=
    exists_centralCharacter_compactScalarSupport (⟨⟩ : LocalFieldData F) ρ hρ hi
  let z := matrixUniformizer F n
  let ω := χ z
  have hz := matrixUniformizer_det_abs_lt_one F n
  have hzi : GeneralLinear.inverseTranspose (n + 1) F z.val = (z⁻¹).val := by
    change GeneralLinear.inverseTranspose (n + 1) F
      (GeneralLinear.scalar (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
        (⟨⟩ : LocalFieldData F))) =
      (GeneralLinear.scalar (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
        (⟨⟩ : LocalFieldData F)))⁻¹
    rw [GeneralLinear.inverseTranspose_scalar, map_inv]
  have hcov (f : biSmoothMatrixCoefficients ρ) (g) :
      f.val (z.val * g) = (ω : ℂ) * f.val g :=
    (hf f).2.1 z g
  have hcovI (f : biSmoothMatrixCoefficients ρ) (g) :
      coefficientIota f.val (z.val * g) =
        ((ω⁻¹ : ℂˣ) : ℂ) * coefficientIota f.val g := by
    change f.val (GeneralLinear.inverseTranspose (n + 1) F (z.val * g)) = _
    rw [map_mul, hzi]
    simpa only [map_inv, ω, coefficientIota] using
      (hf f).2.1 z⁻¹ (GeneralLinear.inverseTranspose (n + 1) F g)
  have hI (f : biSmoothMatrixCoefficients ρ) :
      Continuous (coefficientIota f.val) ∧
        ∃ K : Set (Langlands.GeneralLinear (n + 1) F),
          IsCompact K ∧ Function.support (coefficientIota f.val) ⊆ scalarSaturation K := by
    obtain ⟨K, hK, hs⟩ := (hf f).2.2
    exact ⟨(hf f).1.comp (GeneralLinear.continuous_inverseTranspose _ _),
      _, hK.image (GeneralLinear.continuous_inverseTranspose _ _),
      support_coefficientIota_subset_scalarSaturation f.val K hs⟩
  obtain ⟨a, ha⟩ := exists_halfPlane_norm_matrixRatio_lt_one
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) z.val hz (ω : ℂ) (jpssShift n)
  obtain ⟨aI, haI⟩ := exists_halfPlane_norm_matrixRatio_lt_one
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) z.val hz
    ((ω⁻¹ : ℂˣ) : ℂ) (jpssShift n)
  refine ⟨ω, ⟨?_, ?_, ?_, ?_⟩⟩
  · refine ⟨a, fun Φ f s hs => ?_⟩
    obtain ⟨K, hK, hS⟩ := (hf f).2.2
    obtain ⟨A, hA⟩ := exists_laurent_matrixIntegral_quotient
      F z.val hz ω Φ f.val (hf f).1 (hcov f) K hK hS
    exact (hA s (ha s hs)).1
  · refine ⟨aI, fun Φ f s hs => ?_⟩
    obtain ⟨K, hK, hS⟩ := (hI f).2
    obtain ⟨A, hA⟩ := exists_laurent_matrixIntegral_quotient
      F z.val hz (ω⁻¹ : ℂˣ) Φ (coefficientIota f.val) (hI f).1 (hcovI f) K hK hS
    exact (hA s (haI s hs)).1
  · intro Φ f
    obtain ⟨K, hK, hS⟩ := (hf f).2.2
    exact exists_shiftedRationalValue_of_scalarSaturation
      F z.val hz ω Φ f.val (hf f).1 (hcov f) K hK hS
  · intro Φ f
    obtain ⟨K, hK, hS⟩ := (hI f).2
    exact exists_shiftedRationalValue_of_scalarSaturation
      F z.val hz (ω⁻¹ : ℂˣ) Φ (coefficientIota f.val) (hI f).1 (hcovI f) K hK hS

end Padic

end Langlands.AllField.GodementJacquet
