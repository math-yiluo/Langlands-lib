import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedDualBlock
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBlockConvergence
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedDualTransport
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion
/-! # Exact density, sign and quotient transport of the complementary dual block -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NNReal ENNReal

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement boxLatticeTest_fourier_rightLeadingSign boxLatticeTest_rightLeadingSign compactParametersBorel compactParametersGLBorel compactParametersGLLocallyCompact compactParametersGLMeasurable compactParametersGLSecondCountable compactParametersLocalField compactParametersMeasurable compactParametersNBorel compactParametersNMeasurable compactParametersSecondCountable compactParametersT2 compactParametersTopology compactParametersTotallyDisconnected compactParametersValuativeRel continuous_principalSignedBlockPoint determinantNorm_rankOneSignedBlockWeyl determinantNorm_rankOneSignedWeyl determinantNorm_rankOneWeylLeadingSign determinantWeight_principalSignedBlockPoint diagonalConj_map diagonal_abs_bound diagonal_abs_last dualFunction_blockMatrixAt_rankCast exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType glOneWeight_eq_determinantWeight glOneWeight_smul_natSucc integrable_generalLinear_one_natWeight_iff integrable_generalLinear_one_prod_natWeight_iff integrable_principalFixedBlockIntegrand_signedDual_iff integrable_principalModelBlockIntegrand_of_fixed integrable_principalModelFourierIntegrand_signedDual_iff integrable_prod_generalLinear_one_natWeight_iff integrable_rankOneDualBlockIntegrand_iff integral_generalLinear_one_natWeight integral_generalLinear_one_prod_natWeight integral_principalFixedBlockIntegrand_signedDual integral_principalModelBlockIntegrand_of_fixed integral_principalModelFourierIntegrand_signedDual integral_prod_generalLinear_one_natWeight integral_rankOneDualBlockIntegrand isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow orbitBlocksBorel orbitBlocksLocalField orbitBlocksMeasurable orbitBlocksNBorel orbitBlocksNLocallyCompact orbitBlocksNMeasurable orbitBlocksNSecondCountable orbitBlocksSecondCountable orbitBlocksSigmaCompact orbitBlocksT2 orbitBlocksTopology orbitBlocksTotallyDisconnected orbitBlocksValuativeRel padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType parameter_glOneMeasure_block_density parameter_glOneMeasure_density principalCompactDualBorel principalCompactDualGLBorel principalCompactDualGLMeasurable principalCompactDualGLSecondCountable principalCompactDualIntegrand principalCompactDualIntegrand_reconstruct principalCompactDualLocalField principalCompactDualMeasurable principalCompactDualSecondCountable principalCompactDualT2 principalCompactDualTopology principalCompactDualTotallyDisconnected principalCompactDualUnitsBorel principalCompactDualUnitsMeasurable principalCompactDualUnitsSecondCountable principalCompactDualValuativeRel principalCompactDual_fourierOrbit_duality principalCompactDual_pairing principalCompactDual_pairing_weighted principalCompactFourier_reconstruct principalCompactKernel principalCompactKernel_ae principalCompactKernel_detNorm principalCompactKernel_of_mem principalFixedBlockIntegrand principalFixedBlockIntegrand_density principalFixedDualBorel principalFixedDualGLBorel principalFixedDualGLMeasurable principalFixedDualGLSecondCountable principalFixedDualLocalField principalFixedDualMeasurable principalFixedDualSecondCountable principalFixedDualT2 principalFixedDualTopology principalFixedDualTotallyDisconnected principalFixedDualValuativeRel principalFixedModelDual_pairing principalModelBlockIntegrand principalModelBlockIntegrand_ae_of_fixed principalModelDualBorel principalModelDualGLBorel principalModelDualGLMeasurable principalModelDualGLSecondCountable principalModelDualLocalField principalModelDualMeasurable principalModelDualSecondCountable principalModelDualT2 principalModelDualTopology principalModelDualTotallyDisconnected principalModelDualValuativeRel principalModelDual_pairing principalModelFourierIntegrand principalModelFourierIntegrand_signedDual_eq principalSignedBlockPoint rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneDualBlockIntegrand rankOneDualBlockIntegrand_eq_quotient rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneSignedDualHomeomorph rankOneSignedDualHomeomorph_apply rankOneSignedDualHomeomorph_preserving rankOneWhittakerType rankOne_blockZero_exists_ne_zero scalarHaarBorel scalarHaarGLBorel scalarHaarGLLocallyCompact scalarHaarGLMeasurable scalarHaarGLSecondCountable scalarHaarLocalField scalarHaarMeasurable scalarHaarNullSingleton scalarHaarSecondCountable scalarHaarSigmaCompact scalarHaarT2 scalarHaarTopology scalarHaarValuativeRel signedBlockGLParameterIntegrand signedDualBlockGLBorel signedDualBlockGLMeasurable signedDualBlockGLSigmaCompact signedDualBlockLocalField signedDualBlockQuotientBorel signedDualBlockQuotientMeasurable signedDualBlockScalarBorel signedDualBlockScalarMeasurable signedDualBlockSecondCountable signedDualBlockT2 signedDualBlockTopology signedDualBlockUnipotentBorel signedDualBlockUnipotentMeasurable signedDualBlockValuation signedDualTransportGLBorel signedDualTransportGLMeasurable signedDualTransportLocalField signedDualTransportScalarMeasurable signedDualTransportTopology signedDualTransportValuation signedWeylGLParameterIntegrand signedWeylGL_blockGL_parameter_duality signedWeylOrbit_blockOrbit_fourier_duality signedWeylOrbit_blockOrbit_fourier_duality_averaged signedWeyl_affineBlock_fourier_duality singleton_modulus_real tsupport_boxLatticeTest_subset unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan weylBlockBorelSpace weylBlockLocalField weylBlockMeasurableSpace weylBlockNBorelSpace weylBlockNLocallyCompact weylBlockNMeasurableSpace weylBlockNSecondCountable weylBlockSecondCountable weylBlockSigmaCompact weylBlockT2 weylBlockTopology weylBlockTotallyDisconnected weylBlockValuativeRel zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.Conductor
open Langlands.RankinSelberg.RankOneIwasawa hiding ColBound abv_det_eq_one ae_outerMeasure_mem colBound_of_inv colBound_zero congruenceGroup congruenceGroup_anti congruenceGroup_le_integral conj_mem_congruenceGroup continuous_det_units continuous_point continuous_torusCoord continuous_torusModulus continuous_weight det_point det_unipotent_mul determinantWeight_diagPoint diagPoint diagPoint_mul diagonalUnits_mem_congruenceGroup elemUnipotent elemUnipotent_val exists_compact_hFamily exists_congruenceGroup_le exists_cornerSchwartz exists_lattice_nontrivial exists_lattice_subset exists_mem_lattice exists_mem_matLattice exists_model_congruence exists_model_hFamily exists_ne_zero_of_unipotentTransform_ne_zero exists_rankOneModel_of_matrix exists_schwartz_congruence glLocallyCompact glLocallyCompactU glModelFunction_sum glOneMeasure glOneMeasure_sigmaFinite glSecondCountable glSecondCountableE glSecondCountableU hFamily hFamily_finite hFamily_mul_right hProduct hProduct_mul_right instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceGeneralLinearHAddNatOfNatCarrier_2 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instBorelSpaceUnitsCarrier instBorelSpaceUnitsCarrier_2 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instIsNonarchimedeanLocalFieldCarrier_4 instIsNonarchimedeanLocalFieldCarrier_5 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_2 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instMeasurableSpaceUnitsCarrier instMeasurableSpaceUnitsCarrier_1 instMeasurableSpaceUnitsCarrier_2 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instSecondCountableTopologyCarrier_2 instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instTopologicalSpaceCarrier_4 instTopologicalSpaceCarrier_5 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 instValuativeRelCarrier_4 instValuativeRelCarrier_5 integralSet integralSubgroup_mem_matLattice integral_matrixIntegrand_unfold integral_mul_matLattice inv_mem_lattice_of_notMem inv_mem_of_colBound isCompact_integralSet isCompact_lattice isCompact_unitBox isOpen_congruenceGroup isOpen_lattice isOpen_matLattice isOpen_outerCongruence isOpen_unitsCongruence iwasawaMeasure iwasawaMeasure_point_preimage iwasawaMeasure_sFinite lattice_mono lattice_mul map_iwasawaMeasure_prod map_unfoldedMeasure matLattice matLattice_basis matLattice_mono matLattice_mul matLattice_mul_integral matrixIntegrand_unfoldedPoint matrixLocallyCompact matrixLocallyCompactE matrixLocallyCompactU measurable_point measurable_unfoldedPoint measurePreserving_shift mem_lattice_zero_iff mem_matLattice mem_matLattice_of_support mul_sub_one_mem one_add_mem_lattice_zero one_add_single_apply one_mem_lattice_zero one_mem_outerCongruence outerCongruence outerMeasure outerMeasure_sFinite parameterBase_isMulLeftInvariant parameterMeasure parameterMeasure_eq_prod parameterMeasure_sigmaFinite schwartzOfLattice schwartzOfLattice_apply schwartz_invariance schwartz_support_bound standardCharacter_elemUnipotent tailMeasure tailMeasure_sigmaFinite torusCoord_one_mem torusModulus torusModulus_apply torusModulus_cons_one torusModulus_eq_one unfoldedMeasure unfoldedMeasure_eq unfoldedPoint unfoldedPoint_eq unipotentConj_map unipotentLocallyCompact unipotentLocallyCompactU unipotentSecondCountable unipotentSecondCountableU unipotentTransform unipotentTransform_diag_bounds unipotentTransform_eq_zero_of_shift unipotentTransform_mul_right unipotent_col_zero unipotent_mul_single_zero unitsCongruence unitsSecondCountable unitsSecondCountableE weight weight_apply weight_glOne weight_smul_determinantWeight weight_split whittakerRationalValues_subset_rankOneModelValues
open Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg.RankOneBox hiding ModelBoxConditions PrincipalModelRealization PrincipalOriginalAssertions averagedModelCoefficient_eq_of_left_invariant box boxCoefficientBorelSpace boxCoefficientLocalField boxCoefficientMeasurableSpace boxCoefficientTopology boxCoefficientValuativeRel boxCoefficient_extraction_of_principalLevel boxCoefficient_mul_principalLevel boxCoefficient_point boxComparisonVolume boxConvergenceBorelSpace boxConvergenceLocalField boxConvergenceMeasurableSpace boxConvergenceSecondCountable boxConvergenceT2 boxConvergenceTopology boxConvergenceUnipotentBorel boxConvergenceUnipotentMeasurable boxConvergenceUnitsBorel boxConvergenceUnitsMeasurable boxConvergenceUnitsSecondCountable boxConvergenceValuativeRel boxEntry boxExtractionConstant boxExtractionConstant_pos boxLatticeCentre boxLatticeTest boxLatticeTest_apply boxLatticeTest_eq_compactOpenIndicator boxSupport boxVolumeBorelSpace boxVolumeLocalField boxVolumeMeasurableSpace boxVolumeTopology boxVolumeUnipotentBorel boxVolumeUnipotentMeasurable boxVolumeValuativeRel box_comparison_of_integrable box_eq_pi box_eq_rectangularLatticeCoset box_matrixIntegrand_eq_of_eq_on_box coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_principalAverage continuous_rankOneEmbedding continuous_unipotent_entry cutoffUnipotent_mem_principalLevel determinantRankOne_point determinantWeight_mul_of_norm_one determinantWeight_rankOneEmbedding determinantWeighted_equivariant diagonalUnits_mem_principalLevel exists_box_averagedModelCoefficient_eq exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box exists_principalModelRealization glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isCompact_unipotentBox isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel levelSet_eq_additiveLattice lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff modelFunction_eq_determinantRankOne_of_mem_box modelFunction_eq_determinantRankOne_of_mem_box_of_le mul_mem_box mul_mem_box_iff mul_mem_box_iff_of_le mul_mem_box_of_le mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalAverage principalAverageGLBorel principalAverageGLLocallyCompact principalAverageGLMeasurable principalAverageGLSecondCountable principalAverageLocalField principalAverageMatrixLocallyCompact principalAverageT2 principalAverageTopology principalAverageValuativeRel principalAverage_box_integral principalAverage_equivariant principalAverage_extraction principalAverage_mul principalAveragingMeasure principalAveragingMeasure_ae_det_norm principalAveragingMeasure_ae_mem principalAveragingMeasure_finite principalAveragingMeasure_fixed principalAveragingMeasure_integral principalAveragingMeasure_mass principalAveragingMeasure_weighted_integral principalLevel_firstRow principalLevel_le_integral principalLevel_mass_pos principalMeasure_extraction principalMeasure_weighted_extraction principalOriginalAssertions_of_realization principalOriginalGLBorel principalOriginalGLMeasurable principalOriginalLocalField principalOriginalTopology principalOriginalValuativeRel principalOriginal_value principalRealizationGLBorel principalRealizationGLMeasurable principalRealizationLocalField principalRealizationTopology principalRealizationValuativeRel principalWeightedGLBorel principalWeightedGLMeasurable principalWeightedLocalField principalWeightedScalarAverage principalWeightedTopology principalWeightedValuativeRel rankOneEmbedding_eq_point rankOneModelValues_subset rankOneModel_convergesOnRight_of_matrix rankOne_support_of_principalLevel restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem uniformBoxGLBorel uniformBoxGLMeasurable uniformBoxLocalField uniformBoxSecondCountable uniformBoxT2 uniformBoxTopology uniformBoxUnipotentBorel uniformBoxUnipotentMeasurable uniformBoxUnitsBorel uniformBoxUnitsMeasurable uniformBoxUnitsSecondCountable uniformBoxValuativeRel uniformBox_mul_principalLevel uniform_box_extraction unipotentBox unipotentBox_eq_entry_preimage unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_lt_top_all unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
open Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg.AdjacentBlockReduction
open Langlands.QuotientIntegration

universe uF uV
variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance signedDualBlockT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance signedDualBlockSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance signedDualBlockScalarMeasurable : MeasurableSpace F := borel _
local instance signedDualBlockScalarBorel : BorelSpace F := ⟨rfl⟩
local instance signedDualBlockGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance signedDualBlockGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance signedDualBlockGLSigmaCompact (n : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (n + 1)
local instance signedDualBlockUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F) := borel _
local instance signedDualBlockUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F) := ⟨rfl⟩
local instance signedDualBlockQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F) := borel _
local instance signedDualBlockQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The literal unsigned complementary dual block on the actual GL₁ product. -/
def rankOneDualBlockIntegrand (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F) : ℂ :=
  dualFunction (m + 1) W
      (blockMatrixAt m 0 (by omega) z.1 z.2 * blockWeylAt 0 (m + 1) (by omega)) *
    determinantWeight abv z.1 (s - ((m + 1 : ℕ) : ℂ) / 2)

/-- The density acts on the complete weighted integrand with exactly the JPSS shift. -/
theorem principalFixedBlockIntegrand_density (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F) :
    weight F (m + 1) (z.1, 1) •
      principalFixedBlockIntegrand F m (s + GodementJacquet.jpssShift (m + 1)) W z =
    W (blockMatrixAt m 0 (by omega) z.1 z.2 *
        rankOneSignedBlockWeyl (m + 1) (by omega)) *
      determinantWeight abv z.1 (s - ((m + 1 : ℕ) : ℂ) / 2) := by
  unfold principalFixedBlockIntegrand
  rw [mul_comm (determinantWeight _ _ _)]
  exact weight_smul_determinantWeight F z.1 s _

/-- Density and alternating rectangular signs preserve genuine block convergence. -/
theorem integrable_principalFixedBlockIntegrand_signedDual_iff
    (ν : AdditiveHaarMeasure F) (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F → ℂ) :
    Integrable (principalFixedBlockIntegrand F m (s + GodementJacquet.jpssShift (m + 1))
      (rankOneSignedDualFunction (m + 1) W))
      ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) ↔
    Integrable (rankOneDualBlockIntegrand F m s W)
      ((generalLinearHaar F 0).prod (rectangularMeasure ν m 1)) := by
  have hw : Measurable fun g : Langlands.GeneralLinear 1 F =>
      weight F (m + 1) (g, 1) :=
    ((continuous_weight F (m + 1)).comp (continuous_id.prodMk continuous_const)).measurable
  have hwp : Measurable fun z :
      Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F =>
      weight F (m + 1) (z.1, 1) := hw.comp measurable_fst
  rw [glOneMeasure, prod_withDensity_left hw.coe_nnreal_ennreal,
    integrable_withDensity_iff_integrable_smul hwp]
  have he :
      (fun z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F =>
        weight F (m + 1) (z.1, 1) •
          principalFixedBlockIntegrand F m (s + GodementJacquet.jpssShift (m + 1))
            (rankOneSignedDualFunction (m + 1) W) z) =
      (fun z => determinantWeight abv z.1 (s - ((m + 1 : ℕ) : ℂ) / 2) *
        rankOneSignedDualFunction (m + 1) W
          (blockMatrixAt m 0 (by omega) z.1 z.2 *
            rankOneSignedBlockWeyl (m + 1) (by omega))) := by
    funext z
    rw [principalFixedBlockIntegrand_density, mul_comm]
  rw [he]
  have h := integrable_rankOneSignedDualFunction_block_iff ν
    (generalLinearHaar F 0) m abv (s - ((m + 1 : ℕ) : ℂ) / 2) W
  unfold rankOneDualBlockIntegrand
  simpa only [mul_comm] using h

/-- The two substitutions contribute no scalar to the complete block integral. -/
theorem integral_principalFixedBlockIntegrand_signedDual
    (ν : AdditiveHaarMeasure F) (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F → ℂ) :
    (∫ z, principalFixedBlockIntegrand F m (s + GodementJacquet.jpssShift (m + 1))
      (rankOneSignedDualFunction (m + 1) W) z
      ∂(glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) =
    ∫ z, rankOneDualBlockIntegrand F m s W z
      ∂(generalLinearHaar F 0).prod (rectangularMeasure ν m 1) := by
  have hw : Measurable fun g : Langlands.GeneralLinear 1 F =>
      weight F (m + 1) (g, 1) :=
    ((continuous_weight F (m + 1)).comp (continuous_id.prodMk continuous_const)).measurable
  have hwp : Measurable fun z :
      Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F =>
      weight F (m + 1) (z.1, 1) := hw.comp measurable_fst
  rw [glOneMeasure, prod_withDensity_left hw.coe_nnreal_ennreal,
    integral_withDensity_eq_integral_smul hwp]
  simp_rw [principalFixedBlockIntegrand_density]
  have h := integral_rankOneSignedDualFunction_block ν
    (generalLinearHaar F 0) m abv (s - ((m + 1 : ℕ) : ℂ) / 2) W
  simpa only [rankOneDualBlockIntegrand, mul_comm] using h

/-- Rank transport of the actual block agrees with rank transport of the dual function. -/
theorem dualFunction_blockMatrixAt_rankCast
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    (W : WhittakerFunctions ψ r) (j k : ℕ) (hr : r = 0 + (j + k + 1))
    (a : Langlands.GeneralLinear (r + 1) F)
    (g : Langlands.GeneralLinear 1 F)
    (X : Matrix (Fin j) (Fin 1) F) :
    dualFunction r W.val (blockMatrixAt j k hr g X * a) =
      (InducedTailIntermediate.whittakerRankCast (ψ.scale (-1)) hr
        (translateWhittaker (ψ.scale (-1)) r (firstDualFunction ψ r W) a)).val
          (unequalRankMatrix j k g X) := by
  subst r
  rfl

section ActualModel

variable (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
  {m : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (m + 2) F) V)
  (ℓ : glFunctionals ψ (m + 1) σ)
  (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
  (μ : Measure (LeftUnipotentQuotient 0 F))
  (hμ : IsCompatible (upperUnipotent (0 + 1) F) (generalLinearHaar F 0)
    (unipotentHaar F 0) μ)

/-- The actual quotient dual integrand pulls back to the complete GL₁ integrand. -/
theorem rankOneDualBlockIntegrand_eq_quotient (s : ℂ)
    (z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F) :
    rankOneDualBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ w) z =
    unequalRankIntegrand (ψ.scale (-1)) abv m 0
      (InducedTailIntermediate.whittakerRankCast (ψ.scale (-1)) (by omega)
        (translateWhittaker (ψ.scale (-1)) (m + 1) (firstDualFunction ψ (m + 1) w.val)
          (blockWeylAt 0 (m + 1) (by omega))))
      (secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val) s z.2 (Quotient.mk _ z.1) := by
  simp only [unequalRankIntegrand_mk, secondDualFunction_apply, rankOneTrivialModelOne_apply,
    mul_one]
  unfold rankOneDualBlockIntegrand
  rw [show glModelFunction ψ (m + 1) σ ℓ w = w.val.val from rfl,
    dualFunction_blockMatrixAt_rankCast]

include hμ in
/-- Genuine convergence of the Library dual is precisely convergence on the GL₁ product. -/
theorem integrable_rankOneDualBlockIntegrand_iff (s : ℂ) :
    Integrable (rankOneDualBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ w))
      ((generalLinearHaar F 0).prod (rectangularMeasure ν m 1)) ↔
    UnequalRankConverges (ψ.scale (-1)) abv m 0 μ (rectangularMeasure ν m 1)
      (InducedTailIntermediate.whittakerRankCast (ψ.scale (-1)) (by omega)
        (translateWhittaker (ψ.scale (-1)) (m + 1) (firstDualFunction ψ (m + 1) w.val)
          (blockWeylAt 0 (m + 1) (by omega))))
      (secondDualFunction ψ 0 (rankOneTrivialModelOne ψ).val) s := by
  rw [eq_rankOneQuotientHaar_of_isCompatible F μ hμ, UnequalRankConverges,
    Langlands.AllField.RankinSelberg.RankOneBlockConvergence.integrable_quotient_prod_iff F]
  have he := funext (rankOneDualBlockIntegrand_eq_quotient F ψ σ ℓ w s)
  rw [← he]

include hμ in
/-- Fubini and the actual rank-one quotient identify the genuine dual value. -/
theorem integral_rankOneDualBlockIntegrand (s : ℂ)
    (hi : Integrable (rankOneDualBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ w))
      ((generalLinearHaar F 0).prod (rectangularMeasure ν m 1))) :
    (∫ z, rankOneDualBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ w) z
      ∂(generalLinearHaar F 0).prod (rectangularMeasure ν m 1)) =
    dualUnequalRankModelIntegralAt (by omega) 0 m (by omega) ψ abv μ ν σ
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ (rankOneTrivialInverseFunctional ψ)
      w (rankOneTrivialModelOne ψ) s := by
  rw [dualUnequalRankModelIntegralAt, unequalRankIntegralAt_eq_rankCast, unequalRankIntegral,
    eq_rankOneQuotientHaar_of_isCompatible F μ hμ, integral_rankOneQuotientHaar]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with g
  apply integral_congr_ae
  filter_upwards [] with X
  exact rankOneDualBlockIntegrand_eq_quotient F ψ σ ℓ w s (g, X)

end ActualModel

end Langlands.AllField.RankinSelberg
