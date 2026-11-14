import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalOriginal
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalRealization
/-! # Actual original comparison for the uniform principal realization -/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData averagedModelCoefficient averagedModelCoefficient_apply averagedModelCoefficient_paired_integrals averagingBorelSpace averagingLocalField averagingMeasurableSpace averagingSecondCountable averagingSigmaCompact averagingTopology averagingValuativeRel coefficientIota_averagedModelCoefficient compactOpen_matrixTest_fourier_invariant comparisonAveragingBorelSpace comparisonAveragingLocalField comparisonAveragingMeasurableSpace comparisonAveragingSecondCountable comparisonAveragingSigmaCompact comparisonAveragingTopology comparisonAveragingValuativeRel exists_compactOpen_matrixTest_invariant exists_nhds_matrixTest_invariant fourierAveragingTopology instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 inverseTransposeOpenSubgroup inverseTransposeOpenSubgroup_toSubgroup iotaMatrixRationalValues isCompact_inverseTransposeOpenSubgroup jpssI2 jpssI3 jpssI3_le_jpssI2 matrixIntegral matrixIntegral_normalizedLeftAverage matrixIntegrand matrixRationalValues modelSetIntegral modelSetIntegralDual principalOriginalFourierScalarMeasurable principalOriginalFourierTopology whittakerRationalValues whittakerRationalValues_subset
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero singleton_modulus_real unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg
open scoped NNReal

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance principalOriginalFourierScalarMeasurable : MeasurableSpace F := borel _

/-- Any supplied compact open full-test stabilizer fixes every Fourier partner
on its inverse-transpose side. -/
theorem compactOpen_matrixTest_fourier_invariant {n : ℕ}
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F)))
    (Φ ΦHat : MatrixTestFunction n F) (hpair : MatrixFourierPair F ψ ν Φ ΦHat)
    (hΦ : ∀ k ∈ K, ∀ M, Φ (k.val * M) = Φ M) :
    ∀ k ∈ inverseTransposeOpenSubgroup F K,
      (∀ M, ΦHat (k.val * M) = ΦHat M) ∧
        normalizedAbsoluteValue (⟨⟩ : LocalFieldData F) (Matrix.det k.val) = 1 := by
  have hd := Langlands.AllField.GodementJacquet.padicMatrixFourierPair_compact_left_invariant F
    (⟨⟩ : LocalFieldData F) n ψ ν K.toSubgroup hK Φ ΦHat hpair hΦ
  intro k hk
  constructor
  · apply hd k
    rw [← inverseTransposeOpenSubgroup_toSubgroup F K]
    exact hk
  · have hn := (⟨⟩ : LocalFieldData F).determinantNorm_eq_one_of_mem_compact
      (n + 1) (inverseTransposeOpenSubgroup F K).toSubgroup
      (isCompact_inverseTransposeOpenSubgroup F K hK) k hk
    exact congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hn

end Langlands.AllField.GodementJacquet.Padic

namespace Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg.RankOneBox hiding ModelBoxConditions PrincipalModelRealization PrincipalOriginalAssertions averagedModelCoefficient_eq_of_left_invariant box boxCoefficientBorelSpace boxCoefficientLocalField boxCoefficientMeasurableSpace boxCoefficientTopology boxCoefficientValuativeRel boxCoefficient_extraction_of_principalLevel boxCoefficient_mul_principalLevel boxCoefficient_point boxComparisonVolume boxConvergenceBorelSpace boxConvergenceLocalField boxConvergenceMeasurableSpace boxConvergenceSecondCountable boxConvergenceT2 boxConvergenceTopology boxConvergenceUnipotentBorel boxConvergenceUnipotentMeasurable boxConvergenceUnitsBorel boxConvergenceUnitsMeasurable boxConvergenceUnitsSecondCountable boxConvergenceValuativeRel boxEntry boxExtractionConstant boxExtractionConstant_pos boxLatticeCentre boxLatticeTest boxLatticeTest_apply boxLatticeTest_eq_compactOpenIndicator boxSupport boxVolumeBorelSpace boxVolumeLocalField boxVolumeMeasurableSpace boxVolumeTopology boxVolumeUnipotentBorel boxVolumeUnipotentMeasurable boxVolumeValuativeRel box_comparison_of_integrable box_eq_pi box_eq_rectangularLatticeCoset box_matrixIntegrand_eq_of_eq_on_box coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_principalAverage continuous_rankOneEmbedding continuous_unipotent_entry cutoffUnipotent_mem_principalLevel determinantRankOne_point determinantWeight_mul_of_norm_one determinantWeight_rankOneEmbedding determinantWeighted_equivariant diagonalUnits_mem_principalLevel exists_box_averagedModelCoefficient_eq exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box exists_principalModelRealization glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isCompact_unipotentBox isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel levelSet_eq_additiveLattice lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff modelFunction_eq_determinantRankOne_of_mem_box modelFunction_eq_determinantRankOne_of_mem_box_of_le mul_mem_box mul_mem_box_iff mul_mem_box_iff_of_le mul_mem_box_of_le mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalAverage principalAverageGLBorel principalAverageGLLocallyCompact principalAverageGLMeasurable principalAverageGLSecondCountable principalAverageLocalField principalAverageMatrixLocallyCompact principalAverageT2 principalAverageTopology principalAverageValuativeRel principalAverage_box_integral principalAverage_equivariant principalAverage_extraction principalAverage_mul principalAveragingMeasure principalAveragingMeasure_ae_det_norm principalAveragingMeasure_ae_mem principalAveragingMeasure_finite principalAveragingMeasure_fixed principalAveragingMeasure_integral principalAveragingMeasure_mass principalAveragingMeasure_weighted_integral principalLevel_firstRow principalLevel_le_integral principalLevel_mass_pos principalMeasure_extraction principalMeasure_weighted_extraction principalOriginalAssertions_of_realization principalOriginalGLBorel principalOriginalGLMeasurable principalOriginalLocalField principalOriginalTopology principalOriginalValuativeRel principalOriginal_value principalRealizationGLBorel principalRealizationGLMeasurable principalRealizationLocalField principalRealizationTopology principalRealizationValuativeRel principalWeightedGLBorel principalWeightedGLMeasurable principalWeightedLocalField principalWeightedScalarAverage principalWeightedTopology principalWeightedValuativeRel rankOneEmbedding_eq_point rankOneModelValues_subset rankOneModel_convergesOnRight_of_matrix rankOne_support_of_principalLevel restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem uniformBoxGLBorel uniformBoxGLMeasurable uniformBoxLocalField uniformBoxSecondCountable uniformBoxT2 uniformBoxTopology uniformBoxUnipotentBorel uniformBoxUnipotentMeasurable uniformBoxUnitsBorel uniformBoxUnitsMeasurable uniformBoxUnitsSecondCountable uniformBoxValuativeRel uniformBox_mul_principalLevel uniform_box_extraction unipotentBox unipotentBox_eq_entry_preimage unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_lt_top_all unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
open Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero singleton_modulus_real unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.Conductor
open Langlands.RankinSelberg.RankOneIwasawa hiding ColBound abv_det_eq_one ae_outerMeasure_mem colBound_of_inv colBound_zero congruenceGroup congruenceGroup_le_integral conj_mem_congruenceGroup continuous_det_units continuous_point continuous_torusCoord continuous_torusModulus continuous_weight det_point det_unipotent_mul determinantWeight_diagPoint diagPoint elemUnipotent elemUnipotent_val exists_congruenceGroup_le exists_cornerSchwartz exists_lattice_nontrivial exists_lattice_subset exists_mem_lattice exists_mem_matLattice exists_ne_zero_of_unipotentTransform_ne_zero exists_schwartz_congruence glLocallyCompact glLocallyCompactU glOneMeasure glOneMeasure_sigmaFinite glSecondCountable glSecondCountableU instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instIsNonarchimedeanLocalFieldCarrier_4 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instMeasurableSpaceUnitsCarrier instMeasurableSpaceUnitsCarrier_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instTopologicalSpaceCarrier_4 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 instValuativeRelCarrier_4 integralSet integralSubgroup_mem_matLattice integral_matrixIntegrand_unfold integral_mul_matLattice inv_mem_lattice_of_notMem inv_mem_of_colBound isCompact_lattice isOpen_congruenceGroup isOpen_lattice isOpen_matLattice iwasawaMeasure iwasawaMeasure_point_preimage iwasawaMeasure_sFinite lattice_mono lattice_mul map_iwasawaMeasure_prod map_unfoldedMeasure matLattice matLattice_basis matLattice_mono matLattice_mul matLattice_mul_integral matrixIntegrand_unfoldedPoint matrixLocallyCompact matrixLocallyCompactU measurable_point measurable_unfoldedPoint measurePreserving_shift mem_lattice_zero_iff mem_matLattice mem_matLattice_of_support mul_sub_one_mem one_add_mem_lattice_zero one_add_single_apply one_mem_lattice_zero outerMeasure outerMeasure_sFinite parameterBase_isMulLeftInvariant parameterMeasure parameterMeasure_eq_prod parameterMeasure_sigmaFinite schwartzOfLattice schwartzOfLattice_apply schwartz_invariance schwartz_support_bound standardCharacter_elemUnipotent tailMeasure tailMeasure_sigmaFinite torusModulus torusModulus_apply torusModulus_cons_one torusModulus_eq_one unfoldedMeasure unfoldedMeasure_eq unfoldedPoint unfoldedPoint_eq unipotentConj_map unipotentLocallyCompact unipotentLocallyCompactU unipotentSecondCountable unipotentSecondCountableU unipotentTransform unipotentTransform_diag_bounds unipotentTransform_eq_zero_of_shift unipotentTransform_mul_right unipotent_col_zero unipotent_mul_single_zero unitsSecondCountable weight weight_apply weight_glOne weight_split
open Langlands.AllField.RankinSelberg.RankOneIwasawa
open scoped NNReal ENNReal

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance principalOriginalGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance principalOriginalGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable (ψ : UnitaryAdditiveCharacter F) {m : ℕ} {V : Type uV}
  [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V)
  (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)

/-- The fixed uniform box has exactly its stated positive extraction constant
against the original rank-one integral, at each convergent matrix exponent. -/
theorem principalOriginal_value (hσ : IsSmooth σ) {a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ (⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    (hfixed : ∀ y ∈ principalLevelSubgroup F (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ w (g * y) = glModelFunction ψ (m + 1) σ ℓ w g)
    (s : ℂ)
    (hconv : Integrable (GodementJacquet.matrixIntegrand abv
      (boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a)
      (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w))
      (generalLinearHaar F (m + 1))) :
    GodementJacquet.matrixIntegral abv (generalLinearHaar F (m + 1))
      (boxLatticeTest F ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
        ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a)
      (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) =
    (boxExtractionConstant F (n := m + 1)
      ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
      ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a : ℂ) *
      ∫ g, rankOneModelIntegrand ψ abv σ ℓ w s g ∂generalLinearHaar F 0 := by
  let C := boxExtractionConstant F (n := m + 1)
    ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a
  have hC : 0 ≤ C := (boxExtractionConstant_pos F hA ha).le
  obtain ⟨-, hv⟩ := principalMeasure_weighted_extraction F ψ ha hA
    (glModelFunction ψ (m + 1) σ ℓ w) (continuous_glModelFunction F ψ σ hσ ℓ w)
    (glModelFunction_equivariance ψ (m + 1) σ ℓ w)
    (s + GodementJacquet.jpssShift (m + 1)) hconv
  dsimp only [C] at hC
  simp only [principalWeightedScalarAverage, principalAveragingMeasure_fixed F a hC _ hfixed,
    mul_assoc, integral_const_mul] at hv
  rw [hv]
  congr 1
  have hwm : Measurable fun g : Langlands.GeneralLinear (0 + 1) F =>
      weight F (m + 1) (g, 1) :=
    ((continuous_weight F (m + 1)).comp (continuous_id.prodMk continuous_const)).measurable
  rw [glOneMeasure, integral_withDensity_eq_integral_smul hwm]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
    weight_smul_integrand F ψ σ ℓ w s g)

/-- The actual uniform realization has a common half-plane of genuine original
matrix convergence and the original rank-one value with its prescribed scalar. -/
def PrincipalOriginalAssertions (hσ : IsSmooth σ) (a : ℕ)
    (K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F))) : Prop :=
  let c := (⟨⟩ : LocalFieldData F).additiveConductor ψ
  let Φ := boxLatticeTest F (n := m + 1) (c + a) c a
  let f := Langlands.AllField.GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w
  let C := boxExtractionConstant F (n := m + 1) (c + a) c a
  ∃ b : ℝ, ∀ s : ℂ, b < s.re →
    Integrable (GodementJacquet.matrixIntegrand abv Φ
      (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w))
      (generalLinearHaar F (m + 1)) ∧
    GodementJacquet.matrixIntegral abv (generalLinearHaar F (m + 1)) Φ
      (s + GodementJacquet.jpssShift (m + 1)) f.val =
      (C : ℂ) * ∫ g, rankOneModelIntegrand ψ abv σ ℓ w s g
        ∂generalLinearHaar F 0

/-- No raw convergence assumption is added: matrix convergence of the actual
bi-smooth realization gives raw convergence by pointwise equality on the box. -/
theorem principalOriginalAssertions_of_realization (hσ : IsSmooth σ) {a : ℕ}
    (K : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (m + 1 + 1) F)))
    (hp : PrincipalModelRealization F ψ σ ℓ w hσ a K hK)
    (hMatrix : Langlands.AllField.GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
      (glModelRepresentation ψ (m + 1) σ ℓ)) :
    PrincipalOriginalAssertions F ψ σ ℓ w hσ a K hK := by
  obtain ⟨b, hb⟩ := hMatrix
  refine ⟨b, fun s hs => ?_⟩
  let c := (⟨⟩ : LocalFieldData F).additiveConductor ψ
  let Φ := boxLatticeTest F (n := m + 1) (c + a) c a
  let f := Langlands.AllField.GodementJacquet.Padic.averagedModelCoefficient F ψ σ hσ ℓ K hK w
  have he : GodementJacquet.matrixIntegrand abv Φ
      (s + GodementJacquet.jpssShift (m + 1)) f.val =
    GodementJacquet.matrixIntegrand abv Φ
      (s + GodementJacquet.jpssShift (m + 1)) (glModelFunction ψ (m + 1) σ ℓ w) := by
    dsimp only [Φ]
    rw [boxLatticeTest_eq_compactOpenIndicator]
    exact box_matrixIntegrand_eq_of_eq_on_box F hp.2.2.2.2.2.1 _
  have hc := hb Φ f s hs
  change Integrable _ _ at hc
  rw [he] at hc
  refine ⟨hc, ?_⟩
  change (∫ g, GodementJacquet.matrixIntegrand _ _ _ f.val g ∂_) = _
  rw [he]
  exact principalOriginal_value F ψ σ ℓ w hσ hp.1 hp.2.1 hp.2.2.1 s hc

end Langlands.AllField.RankinSelberg.RankOneBox
