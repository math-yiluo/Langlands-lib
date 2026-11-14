import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalFixedDual
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalModelDual
/-! Removing the same principal parameter for a genuinely principal-fixed function. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped NNReal ENNReal

namespace Langlands.AllField.Conductor
open Langlands.Conductor
open Langlands.AllField.Conductor

open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
universe uK

end Langlands.AllField.Conductor

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement compactParametersBorel compactParametersGLBorel compactParametersGLLocallyCompact compactParametersGLMeasurable compactParametersGLSecondCountable compactParametersLocalField compactParametersMeasurable compactParametersNBorel compactParametersNMeasurable compactParametersSecondCountable compactParametersT2 compactParametersTopology compactParametersTotallyDisconnected compactParametersValuativeRel continuous_principalSignedBlockPoint determinantNorm_rankOneSignedBlockWeyl determinantWeight_principalSignedBlockPoint diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType glOneWeight_eq_determinantWeight glOneWeight_smul_natSucc integrable_generalLinear_one_natWeight_iff integrable_generalLinear_one_prod_natWeight_iff integrable_principalModelBlockIntegrand_of_fixed integrable_prod_generalLinear_one_natWeight_iff integral_generalLinear_one_natWeight integral_generalLinear_one_prod_natWeight integral_principalModelBlockIntegrand_of_fixed integral_prod_generalLinear_one_natWeight isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow orbitBlocksBorel orbitBlocksLocalField orbitBlocksMeasurable orbitBlocksNBorel orbitBlocksNLocallyCompact orbitBlocksNMeasurable orbitBlocksNSecondCountable orbitBlocksSecondCountable orbitBlocksSigmaCompact orbitBlocksT2 orbitBlocksTopology orbitBlocksTotallyDisconnected orbitBlocksValuativeRel padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType parameter_glOneMeasure_block_density parameter_glOneMeasure_density principalCompactDualBorel principalCompactDualGLBorel principalCompactDualGLMeasurable principalCompactDualGLSecondCountable principalCompactDualIntegrand principalCompactDualIntegrand_reconstruct principalCompactDualLocalField principalCompactDualMeasurable principalCompactDualSecondCountable principalCompactDualT2 principalCompactDualTopology principalCompactDualTotallyDisconnected principalCompactDualUnitsBorel principalCompactDualUnitsMeasurable principalCompactDualUnitsSecondCountable principalCompactDualValuativeRel principalCompactDual_fourierOrbit_duality principalCompactDual_pairing principalCompactDual_pairing_weighted principalCompactFourier_reconstruct principalCompactKernel principalCompactKernel_ae principalCompactKernel_detNorm principalCompactKernel_of_mem principalFixedBlockIntegrand principalFixedDualBorel principalFixedDualGLBorel principalFixedDualGLMeasurable principalFixedDualGLSecondCountable principalFixedDualLocalField principalFixedDualMeasurable principalFixedDualSecondCountable principalFixedDualT2 principalFixedDualTopology principalFixedDualTotallyDisconnected principalFixedDualValuativeRel principalFixedModelDual_pairing principalModelBlockIntegrand principalModelBlockIntegrand_ae_of_fixed principalModelDualBorel principalModelDualGLBorel principalModelDualGLMeasurable principalModelDualGLSecondCountable principalModelDualLocalField principalModelDualMeasurable principalModelDualSecondCountable principalModelDualT2 principalModelDualTopology principalModelDualTotallyDisconnected principalModelDualValuativeRel principalModelDual_pairing principalModelFourierIntegrand principalSignedBlockPoint rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero scalarHaarBorel scalarHaarGLBorel scalarHaarGLLocallyCompact scalarHaarGLMeasurable scalarHaarGLSecondCountable scalarHaarLocalField scalarHaarMeasurable scalarHaarNullSingleton scalarHaarSecondCountable scalarHaarSigmaCompact scalarHaarT2 scalarHaarTopology scalarHaarValuativeRel signedBlockGLParameterIntegrand signedWeylGLParameterIntegrand signedWeylGL_blockGL_parameter_duality signedWeylOrbit_blockOrbit_fourier_duality signedWeylOrbit_blockOrbit_fourier_duality_averaged signedWeyl_affineBlock_fourier_duality singleton_modulus_real tsupport_boxLatticeTest_subset unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan weylBlockBorelSpace weylBlockLocalField weylBlockMeasurableSpace weylBlockNBorelSpace weylBlockNLocallyCompact weylBlockNMeasurableSpace weylBlockNSecondCountable weylBlockSecondCountable weylBlockSigmaCompact weylBlockT2 weylBlockTopology weylBlockTotallyDisconnected weylBlockValuativeRel zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.Induction hiding SmoothRep
open Langlands.Conductor
open Langlands.AllField.Conductor
open Langlands.RankinSelberg.RankOneIwasawa hiding ColBound abv_det_eq_one ae_outerMeasure_mem colBound_of_inv colBound_zero congruenceGroup congruenceGroup_le_integral conj_mem_congruenceGroup continuous_det_units continuous_point continuous_torusCoord continuous_torusModulus continuous_weight det_point det_unipotent_mul determinantWeight_diagPoint diagPoint elemUnipotent elemUnipotent_val exists_congruenceGroup_le exists_cornerSchwartz exists_lattice_nontrivial exists_lattice_subset exists_mem_lattice exists_mem_matLattice exists_ne_zero_of_unipotentTransform_ne_zero exists_schwartz_congruence glLocallyCompact glLocallyCompactU glOneMeasure glOneMeasure_sigmaFinite glSecondCountable glSecondCountableU instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instIsNonarchimedeanLocalFieldCarrier_4 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instMeasurableSpaceUnitsCarrier instMeasurableSpaceUnitsCarrier_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instTopologicalSpaceCarrier_4 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 instValuativeRelCarrier_4 integralSet integralSubgroup_mem_matLattice integral_matrixIntegrand_unfold integral_mul_matLattice inv_mem_lattice_of_notMem inv_mem_of_colBound isCompact_lattice isOpen_congruenceGroup isOpen_lattice isOpen_matLattice iwasawaMeasure iwasawaMeasure_point_preimage iwasawaMeasure_sFinite lattice_mono lattice_mul map_iwasawaMeasure_prod map_unfoldedMeasure matLattice matLattice_basis matLattice_mono matLattice_mul matLattice_mul_integral matrixIntegrand_unfoldedPoint matrixLocallyCompact matrixLocallyCompactU measurable_point measurable_unfoldedPoint measurePreserving_shift mem_lattice_zero_iff mem_matLattice mem_matLattice_of_support mul_sub_one_mem one_add_mem_lattice_zero one_add_single_apply one_mem_lattice_zero outerMeasure outerMeasure_sFinite parameterBase_isMulLeftInvariant parameterMeasure parameterMeasure_eq_prod parameterMeasure_sigmaFinite schwartzOfLattice schwartzOfLattice_apply schwartz_invariance schwartz_support_bound standardCharacter_elemUnipotent tailMeasure tailMeasure_sigmaFinite torusModulus torusModulus_apply torusModulus_cons_one torusModulus_eq_one unfoldedMeasure unfoldedMeasure_eq unfoldedPoint unfoldedPoint_eq unipotentConj_map unipotentLocallyCompact unipotentLocallyCompactU unipotentSecondCountable unipotentSecondCountableU unipotentTransform unipotentTransform_diag_bounds unipotentTransform_eq_zero_of_shift unipotentTransform_mul_right unipotent_col_zero unipotent_mul_single_zero unitsSecondCountable weight weight_apply weight_glOne weight_split
open Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg.RankOneBox hiding ModelBoxConditions averagedModelCoefficient_eq_of_left_invariant box boxCoefficientBorelSpace boxCoefficientLocalField boxCoefficientMeasurableSpace boxCoefficientTopology boxCoefficientValuativeRel boxCoefficient_extraction_of_principalLevel boxCoefficient_mul_principalLevel boxCoefficient_point boxComparisonVolume boxConvergenceBorelSpace boxConvergenceLocalField boxConvergenceMeasurableSpace boxConvergenceSecondCountable boxConvergenceT2 boxConvergenceTopology boxConvergenceUnipotentBorel boxConvergenceUnipotentMeasurable boxConvergenceUnitsBorel boxConvergenceUnitsMeasurable boxConvergenceUnitsSecondCountable boxConvergenceValuativeRel boxEntry boxExtractionConstant boxExtractionConstant_pos boxLatticeCentre boxLatticeTest boxLatticeTest_apply boxLatticeTest_eq_compactOpenIndicator boxSupport boxVolumeBorelSpace boxVolumeLocalField boxVolumeMeasurableSpace boxVolumeTopology boxVolumeUnipotentBorel boxVolumeUnipotentMeasurable boxVolumeValuativeRel box_comparison_of_integrable box_eq_pi box_eq_rectangularLatticeCoset box_matrixIntegrand_eq_of_eq_on_box coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_principalAverage continuous_rankOneEmbedding continuous_unipotent_entry cutoffUnipotent_mem_principalLevel determinantRankOne_point determinantWeight_mul_of_norm_one determinantWeight_rankOneEmbedding determinantWeighted_equivariant diagonalUnits_mem_principalLevel exists_box_averagedModelCoefficient_eq exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isCompact_unipotentBox isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel levelSet_eq_additiveLattice lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff modelFunction_eq_determinantRankOne_of_mem_box mul_mem_box mul_mem_box_iff mul_mem_box_iff_of_le mul_mem_box_of_le mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalAverage principalAverageGLBorel principalAverageGLLocallyCompact principalAverageGLMeasurable principalAverageGLSecondCountable principalAverageLocalField principalAverageMatrixLocallyCompact principalAverageT2 principalAverageTopology principalAverageValuativeRel principalAverage_box_integral principalAverage_equivariant principalAverage_extraction principalAverage_mul principalAveragingMeasure principalAveragingMeasure_ae_det_norm principalAveragingMeasure_ae_mem principalAveragingMeasure_finite principalAveragingMeasure_fixed principalAveragingMeasure_integral principalAveragingMeasure_mass principalAveragingMeasure_weighted_integral principalLevel_firstRow principalLevel_le_integral principalLevel_mass_pos principalMeasure_extraction principalMeasure_weighted_extraction principalWeightedGLBorel principalWeightedGLMeasurable principalWeightedLocalField principalWeightedScalarAverage principalWeightedTopology principalWeightedValuativeRel rankOneEmbedding_eq_point rankOneModelValues_subset rankOneModel_convergesOnRight_of_matrix rankOne_support_of_principalLevel restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem uniformBoxGLBorel uniformBoxGLMeasurable uniformBoxLocalField uniformBoxSecondCountable uniformBoxT2 uniformBoxTopology uniformBoxUnipotentBorel uniformBoxUnipotentMeasurable uniformBoxUnitsBorel uniformBoxUnitsMeasurable uniformBoxUnitsSecondCountable uniformBoxValuativeRel uniformBox_mul_principalLevel uniform_box_extraction unipotentBox unipotentBox_eq_entry_preimage unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_lt_top_all unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
open Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg.CompactWhittakerSynthesis hiding compactMatrixLift compactMatrixLift_orbit compactMatrixLift_support compact_signedFourier_pairing continuous_signedFourierOrbitOfCompact exists_signedMatrixOrbit_congruence exists_supported_compactMatrixLift exists_weightedSignedMatrixOrbit_stabilizer firstColumnFrame_mem_range_of_mem_box instValuativeRelCarrier_1 integrable_compact_signedWeyl_fourier_pairing integrable_signedUnipotentMatrixFourierDualKernel integrable_signedUnipotentMatrixFourierOriginalKernel integral_signedUnipotentDualKernel_eq_weightedOrbit integral_signedUnipotentMatrixFourierKernel_fixed integral_signedUnipotentShearedKernel_eq_compactPairing signedCompactPairingBorelSpace signedCompactPairingGLBorelSpace signedCompactPairingGLLocallyCompact signedCompactPairingGLMeasurableSpace signedCompactPairingGLSecondCountable signedCompactPairingLocalField signedCompactPairingMeasurableSpace signedCompactPairingNBorelSpace signedCompactPairingNLocallyCompact signedCompactPairingNMeasurableSpace signedCompactPairingNSecondCountable signedCompactPairingT2 signedCompactPairingTopology signedCompactPairingTotallyDisconnected signedCompactPairingValuativeRel signedFourierOrbitOfCompact signedFourierOrbitOfCompact_left signedFourierOrbitOfCompact_locallyConstant signedMatrixOrbit signedMatrixOrbit_left signedOrbitBorelSpace signedOrbitGLSecondCountable signedOrbitLocalField signedOrbitMeasurableSpace signedOrbitNBorelSpace signedOrbitNLocallyCompact signedOrbitNMeasurableSpace signedOrbitNSecondCountable signedOrbitSecondCountable signedOrbitT2 signedOrbitTopology signedOrbitTotallyDisconnected signedOrbitValuativeRel signedSmoothLocalField signedSmoothNBorel signedSmoothNLocallyCompact signedSmoothNMeasurable signedSmoothTopology signedSmoothValuativeRel signedUnipotentMatrixFourier_exchange supportedSynthesisLocalField supportedSynthesisNBorel supportedSynthesisNMeasurable supportedSynthesisT2 supportedSynthesisTopology supportedSynthesisValuativeRel weightedCompactMatrixLift weightedCompactMatrixLift_orbit weightedCompactMatrixLift_support weightedSignedMatrixOrbit weightedSignedMatrixOrbitSmooth weightedSignedMatrixOrbitSmooth_eval weightedSignedMatrixOrbit_left weightedSignedMatrixOrbit_locallyConstant
open Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg.CompactWhittakerApproximation hiding modelApproximationGLBorel modelApproximationGLLocallyCompact modelApproximationGLMeasurable modelApproximationGLNonarchimedean modelApproximationGLSigmaCompact modelApproximationLocalField modelApproximationT2 modelApproximationTopology modelApproximationValuativeRel weighted_glModel_integral_eq_of_compact
open Langlands.AllField.RankinSelberg.CompactWhittakerApproximation

universe uF uV
variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance principalFixedDualT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance principalFixedDualSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance principalFixedDualMeasurable : MeasurableSpace F := borel _
local instance principalFixedDualBorel : BorelSpace F := ⟨rfl⟩
local instance principalFixedDualGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance principalFixedDualGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance principalFixedDualGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local instance principalFixedDualTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The unaveraged actual signed complementary block, at the same exponent. -/
def principalFixedBlockIntegrand (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F) : ℂ :=
  determinantWeight abv z.1 s *
    W (AdjacentBlockReduction.blockMatrixAt m 0 (by omega) z.1 z.2 *
      rankOneSignedBlockWeyl (m + 1) (by omega))

/-- A principal-fixed function loses no information in the full principal
parameter: its true weighted integrand is almost everywhere constant in it. -/
theorem principalModelBlockIntegrand_ae_of_fixed
    (ν : AdditiveHaarMeasure F) (m a : ℕ) (C : ℝ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (hW : ∀ k ∈ principalLevelSubgroup F (m + 1) a, ∀ g, W (g * k) = W g) :
    principalModelBlockIntegrand F m s W
      =ᵐ[(principalAveragingMeasure F (n := m + 1) a C).prod
        ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))]
      (fun z => principalFixedBlockIntegrand F m s W z.2) := by
  have hk := (Measure.quasiMeasurePreserving_fst
    (μ := principalAveragingMeasure F (n := m + 1) a C)
    (ν := (glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))).ae
    (principalAveragingMeasure_ae_mem F a C)
  filter_upwards [hk] with z hz
  unfold principalModelBlockIntegrand principalSignedBlockPoint principalFixedBlockIntegrand
  rw [hW _ (inverseTranspose_mem_principalLevelSubgroup F (m + 1) a hz)]

/-- Genuine scalar/block convergence implies convergence on the full product
with the same principal averaging parameter, before taking its average. -/
theorem integrable_principalModelBlockIntegrand_of_fixed
    (ν : AdditiveHaarMeasure F) (m a : ℕ) (C : ℝ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (hW : ∀ k ∈ principalLevelSubgroup F (m + 1) a, ∀ g, W (g * k) = W g)
    (hi : Integrable (principalFixedBlockIntegrand F m s W)
      ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) :
    Integrable (principalModelBlockIntegrand F m s W)
      ((principalAveragingMeasure F (n := m + 1) a C).prod
        ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) := by
  have h := (integrable_const (1 : ℂ)
    (μ := principalAveragingMeasure F (n := m + 1) a C)).mul_prod hi
  simp only [one_mul] at h
  exact h.congr (principalModelBlockIntegrand_ae_of_fixed F ν m a C s W hW).symm

/-- The original principal mass is exactly the scalar relating the fixed
block integral to the full product integral. -/
theorem integral_principalModelBlockIntegrand_of_fixed
    (ν : AdditiveHaarMeasure F) (m a : ℕ) {C : ℝ} (hC : 0 ≤ C) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (hW : ∀ k ∈ principalLevelSubgroup F (m + 1) a, ∀ g, W (g * k) = W g) :
    (∫ z, principalModelBlockIntegrand F m s W z
      ∂(principalAveragingMeasure F (n := m + 1) a C).prod
        ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) =
    (C : ℂ) * ∫ z, principalFixedBlockIntegrand F m s W z
      ∂(glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1) := by
  rw [integral_congr_ae (principalModelBlockIntegrand_ae_of_fixed F ν m a C s W hW)]
  calc
    _ = (∫ _k, (1 : ℂ) ∂principalAveragingMeasure F (n := m + 1) a C) *
        ∫ z, principalFixedBlockIntegrand F m s W z
          ∂(glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1) := by
      simpa only [one_mul] using integral_prod_mul
        (fun _k : Langlands.GeneralLinear (m + 2) F => (1 : ℂ))
        (principalFixedBlockIntegrand F m s W)
    _ = _ := by
      simp [integral_const, measureReal_def, principalAveragingMeasure_mass F a hC,
        ENNReal.toReal_ofReal hC, Complex.real_smul]

/-- For an actual principal-fixed coefficient-model vector, the same original
box constant multiplies the actual signed block integral. Scalar/block
convergence supplies the full product bound needed by model approximation. -/
theorem principalFixedModelDual_pairing
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) {m a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ (⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 2) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ (m + 1) σ)
    (f : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) (s : ℂ)
    (hfixed : ∀ k ∈ principalLevelSubgroup F (m + 1) a, ∀ g,
      glModelFunction ψ (m + 1) σ ℓ f (g * k) = glModelFunction ψ (m + 1) σ ℓ f g)
    (hi : Integrable (principalModelFourierIntegrand F ψ ν m a s
        (glModelFunction ψ (m + 1) σ ℓ f)) (generalLinearHaar F (m + 1)))
    (hj : Integrable (principalFixedBlockIntegrand F m s
        (glModelFunction ψ (m + 1) σ ℓ f))
      ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) :
    (∫ h, principalModelFourierIntegrand F ψ ν m a s
      (glModelFunction ψ (m + 1) σ ℓ f) h ∂generalLinearHaar F (m + 1)) =
    (boxExtractionConstant F (n := m + 1)
      ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
      ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a : ℂ) *
      ∫ z, principalFixedBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ f) z
        ∂(glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1) := by
  let C := boxExtractionConstant F (n := m + 1)
    ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a
  have hC : 0 ≤ C := (boxExtractionConstant_pos F (n := m + 1) hA ha).le
  have hraw := integrable_principalModelBlockIntegrand_of_fixed F ν m a C s
    (glModelFunction ψ (m + 1) σ ℓ f) hfixed hj
  exact (principalModelDual_pairing F ψ ν hsd ha hA σ hσ ℓ f s hi hraw).trans
    (integral_principalModelBlockIntegrand_of_fixed F ν m a hC s
      (glModelFunction ψ (m + 1) σ ℓ f) hfixed)

end Langlands.AllField.RankinSelberg
