import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalModelDual
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModelApproximation
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalCompactDual
/-! Extension of compact signed dual extraction to actual coefficient-model vectors. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement compactParametersBorel compactParametersGLBorel compactParametersGLLocallyCompact compactParametersGLMeasurable compactParametersGLSecondCountable compactParametersLocalField compactParametersMeasurable compactParametersNBorel compactParametersNMeasurable compactParametersSecondCountable compactParametersT2 compactParametersTopology compactParametersTotallyDisconnected compactParametersValuativeRel continuous_principalSignedBlockPoint determinantNorm_rankOneSignedBlockWeyl determinantWeight_principalSignedBlockPoint diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType glOneWeight_eq_determinantWeight glOneWeight_smul_natSucc integrable_generalLinear_one_natWeight_iff integrable_generalLinear_one_prod_natWeight_iff integrable_prod_generalLinear_one_natWeight_iff integral_generalLinear_one_natWeight integral_generalLinear_one_prod_natWeight integral_prod_generalLinear_one_natWeight isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow orbitBlocksBorel orbitBlocksLocalField orbitBlocksMeasurable orbitBlocksNBorel orbitBlocksNLocallyCompact orbitBlocksNMeasurable orbitBlocksNSecondCountable orbitBlocksSecondCountable orbitBlocksSigmaCompact orbitBlocksT2 orbitBlocksTopology orbitBlocksTotallyDisconnected orbitBlocksValuativeRel padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType parameter_glOneMeasure_block_density parameter_glOneMeasure_density principalCompactDualBorel principalCompactDualGLBorel principalCompactDualGLMeasurable principalCompactDualGLSecondCountable principalCompactDualIntegrand principalCompactDualIntegrand_reconstruct principalCompactDualLocalField principalCompactDualMeasurable principalCompactDualSecondCountable principalCompactDualT2 principalCompactDualTopology principalCompactDualTotallyDisconnected principalCompactDualUnitsBorel principalCompactDualUnitsMeasurable principalCompactDualUnitsSecondCountable principalCompactDualValuativeRel principalCompactDual_fourierOrbit_duality principalCompactDual_pairing principalCompactDual_pairing_weighted principalCompactFourier_reconstruct principalCompactKernel principalCompactKernel_ae principalCompactKernel_detNorm principalCompactKernel_of_mem principalModelBlockIntegrand principalModelDualBorel principalModelDualGLBorel principalModelDualGLMeasurable principalModelDualGLSecondCountable principalModelDualLocalField principalModelDualMeasurable principalModelDualSecondCountable principalModelDualT2 principalModelDualTopology principalModelDualTotallyDisconnected principalModelDualValuativeRel principalModelDual_pairing principalModelFourierIntegrand principalSignedBlockPoint rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero scalarHaarBorel scalarHaarGLBorel scalarHaarGLLocallyCompact scalarHaarGLMeasurable scalarHaarGLSecondCountable scalarHaarLocalField scalarHaarMeasurable scalarHaarNullSingleton scalarHaarSecondCountable scalarHaarSigmaCompact scalarHaarT2 scalarHaarTopology scalarHaarValuativeRel signedBlockGLParameterIntegrand signedWeylGLParameterIntegrand signedWeylGL_blockGL_parameter_duality signedWeylOrbit_blockOrbit_fourier_duality signedWeylOrbit_blockOrbit_fourier_duality_averaged signedWeyl_affineBlock_fourier_duality singleton_modulus_real tsupport_boxLatticeTest_subset unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan weylBlockBorelSpace weylBlockLocalField weylBlockMeasurableSpace weylBlockNBorelSpace weylBlockNLocallyCompact weylBlockNMeasurableSpace weylBlockNSecondCountable weylBlockSecondCountable weylBlockSigmaCompact weylBlockT2 weylBlockTopology weylBlockTotallyDisconnected weylBlockValuativeRel zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement isClopen_rectangularLatticeCoset isCompact_rectangularLatticeCoset mem_rectangularLatticeCoset padicLatticeGeometry padicRectangularFourierIntegral_exchange_left padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right rectangularLatticeCoset rectangularLatticeCosetTest rectangularLatticeCosetTest_apply
open Langlands.AllField.HarmonicAnalysis
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.Induction hiding SmoothRep
open Langlands.RankinSelberg.RankOneIwasawa hiding ColBound abv_det_eq_one ae_outerMeasure_mem colBound_of_inv colBound_zero congruenceGroup congruenceGroup_le_integral conj_mem_congruenceGroup continuous_det_units continuous_point continuous_torusCoord continuous_torusModulus continuous_weight det_point det_unipotent_mul determinantWeight_diagPoint diagPoint elemUnipotent elemUnipotent_val exists_congruenceGroup_le exists_cornerSchwartz exists_lattice_nontrivial exists_lattice_subset exists_mem_lattice exists_mem_matLattice exists_ne_zero_of_unipotentTransform_ne_zero exists_schwartz_congruence glLocallyCompact glLocallyCompactU glOneMeasure glOneMeasure_sigmaFinite glSecondCountable glSecondCountableU instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instIsNonarchimedeanLocalFieldCarrier_4 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instMeasurableSpaceUnitsCarrier instMeasurableSpaceUnitsCarrier_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instTopologicalSpaceCarrier_4 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 instValuativeRelCarrier_4 integralSet integralSubgroup_mem_matLattice integral_matrixIntegrand_unfold integral_mul_matLattice inv_mem_lattice_of_notMem inv_mem_of_colBound isCompact_lattice isOpen_congruenceGroup isOpen_lattice isOpen_matLattice iwasawaMeasure iwasawaMeasure_point_preimage iwasawaMeasure_sFinite lattice_mono lattice_mul map_iwasawaMeasure_prod map_unfoldedMeasure matLattice matLattice_basis matLattice_mono matLattice_mul matLattice_mul_integral matrixIntegrand_unfoldedPoint matrixLocallyCompact matrixLocallyCompactU measurable_point measurable_unfoldedPoint measurePreserving_shift mem_lattice_zero_iff mem_matLattice mem_matLattice_of_support mul_sub_one_mem one_add_mem_lattice_zero one_add_single_apply one_mem_lattice_zero outerMeasure outerMeasure_sFinite parameterBase_isMulLeftInvariant parameterMeasure parameterMeasure_eq_prod parameterMeasure_sigmaFinite schwartzOfLattice schwartzOfLattice_apply schwartz_invariance schwartz_support_bound standardCharacter_elemUnipotent tailMeasure tailMeasure_sigmaFinite torusModulus torusModulus_apply torusModulus_cons_one torusModulus_eq_one unfoldedMeasure unfoldedMeasure_eq unfoldedPoint unfoldedPoint_eq unipotentConj_map unipotentLocallyCompact unipotentLocallyCompactU unipotentSecondCountable unipotentSecondCountableU unipotentTransform unipotentTransform_diag_bounds unipotentTransform_eq_zero_of_shift unipotentTransform_mul_right unipotent_col_zero unipotent_mul_single_zero unitsSecondCountable weight weight_apply weight_glOne weight_split
open Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg.RankOneBox hiding ModelBoxConditions averagedModelCoefficient_eq_of_left_invariant box boxCoefficientBorelSpace boxCoefficientLocalField boxCoefficientMeasurableSpace boxCoefficientTopology boxCoefficientValuativeRel boxCoefficient_extraction_of_principalLevel boxCoefficient_mul_principalLevel boxCoefficient_point boxComparisonVolume boxConvergenceBorelSpace boxConvergenceLocalField boxConvergenceMeasurableSpace boxConvergenceSecondCountable boxConvergenceT2 boxConvergenceTopology boxConvergenceUnipotentBorel boxConvergenceUnipotentMeasurable boxConvergenceUnitsBorel boxConvergenceUnitsMeasurable boxConvergenceUnitsSecondCountable boxConvergenceValuativeRel boxEntry boxExtractionConstant boxExtractionConstant_pos boxLatticeCentre boxLatticeTest boxLatticeTest_apply boxLatticeTest_eq_compactOpenIndicator boxSupport boxVolumeBorelSpace boxVolumeLocalField boxVolumeMeasurableSpace boxVolumeTopology boxVolumeUnipotentBorel boxVolumeUnipotentMeasurable boxVolumeValuativeRel box_comparison_of_integrable box_eq_pi box_eq_rectangularLatticeCoset box_matrixIntegrand_eq_of_eq_on_box coe_unitLevel continuous_determinantWeight continuous_glModelFunction continuous_principalAverage continuous_rankOneEmbedding continuous_unipotent_entry cutoffUnipotent_mem_principalLevel determinantRankOne_point determinantWeight_mul_of_norm_one determinantWeight_rankOneEmbedding determinantWeighted_equivariant diagonalUnits_mem_principalLevel exists_box_averagedModelCoefficient_eq exists_box_constant exists_mem_principalLevel_mul_inv_upper exists_point_mul_of_mem_box glLocallyCompact glSecondCountable instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceUnitsCarrier instSecondCountableTopologyCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integer_of_mem_principalLevel integral_eq_of_support integral_param_of_eq inv_sub_one_mem_levelSet isCompact_box isCompact_boxEntry isCompact_unipotentBox isOpen_box isOpen_boxEntry isOpen_boxSupport isOpen_torusBox isOpen_unipotentBox isOpen_unitLevel levelSet_eq_additiveLattice lintegral_enorm_eq_of_support lintegral_param_of_eq matrixIntegrand_mul_principalLevel matrixIntegrand_point matrixLocallyCompact measurableSet_integralSubgroup measurePreserving_rshift mem_box_iff mem_box_unipotent_mul_iff mem_torusBox_of_mem_box mem_unitLevel_iff modelFunction_eq_determinantRankOne_of_mem_box mul_mem_box mul_mem_box_iff mul_mem_box_iff_of_le mul_mem_box_of_le mul_sub_one_mem_levelSet one_mem_box one_mem_boxSupport one_mem_unipotentBox parameterBase_isMulLeftInvariant point_eq_mul principalAverage principalAverageGLBorel principalAverageGLLocallyCompact principalAverageGLMeasurable principalAverageGLSecondCountable principalAverageLocalField principalAverageMatrixLocallyCompact principalAverageT2 principalAverageTopology principalAverageValuativeRel principalAverage_box_integral principalAverage_equivariant principalAverage_extraction principalAverage_mul principalAveragingMeasure principalAveragingMeasure_ae_det_norm principalAveragingMeasure_ae_mem principalAveragingMeasure_finite principalAveragingMeasure_fixed principalAveragingMeasure_integral principalAveragingMeasure_mass principalAveragingMeasure_weighted_integral principalLevel_firstRow principalLevel_le_integral principalLevel_mass_pos principalMeasure_extraction principalMeasure_weighted_extraction principalWeightedGLBorel principalWeightedGLMeasurable principalWeightedLocalField principalWeightedScalarAverage principalWeightedTopology principalWeightedValuativeRel rankOneEmbedding_eq_point rankOneModelValues_subset rankOneModel_convergesOnRight_of_matrix rankOne_support_of_principalLevel restrict_boxSupport_lt_top restrict_boxSupport_pos standardCharacter_eq_one tailMeasure_torusBox tailMeasure_torusBox_lt_top tailMeasure_torusBox_pos torusBox torusBox_eq_pi torusFactor_mem uniformBoxGLBorel uniformBoxGLMeasurable uniformBoxLocalField uniformBoxSecondCountable uniformBoxT2 uniformBoxTopology uniformBoxUnipotentBorel uniformBoxUnipotentMeasurable uniformBoxUnitsBorel uniformBoxUnitsMeasurable uniformBoxUnitsSecondCountable uniformBoxValuativeRel uniformBox_mul_principalLevel uniform_box_extraction unipotentBox unipotentBox_eq_entry_preimage unipotentBox_subset unipotentHaar_unipotentBox_lt_top unipotentHaar_unipotentBox_lt_top_all unipotentHaar_unipotentBox_pos unipotentLocallyCompact unipotentSecondCountable unipotent_mul_rankOne_apply unipotent_mul_rankOne_apply_zero unitLevel unitLevel_le_integralUnits unitLevel_measure_le unitLevel_measure_pos unitsSecondCountable weight_smul_integrand
open Langlands.AllField.RankinSelberg.RankOneBox
open Langlands.RankinSelberg.CompactWhittakerSynthesis hiding compactMatrixLift compactMatrixLift_orbit compactMatrixLift_support compact_signedFourier_pairing continuous_signedFourierOrbitOfCompact exists_signedMatrixOrbit_congruence exists_supported_compactMatrixLift exists_weightedSignedMatrixOrbit_stabilizer firstColumnFrame_mem_range_of_mem_box instValuativeRelCarrier_1 integrable_compact_signedWeyl_fourier_pairing integrable_signedUnipotentMatrixFourierDualKernel integrable_signedUnipotentMatrixFourierOriginalKernel integral_signedUnipotentDualKernel_eq_weightedOrbit integral_signedUnipotentMatrixFourierKernel_fixed integral_signedUnipotentShearedKernel_eq_compactPairing signedCompactPairingBorelSpace signedCompactPairingGLBorelSpace signedCompactPairingGLLocallyCompact signedCompactPairingGLMeasurableSpace signedCompactPairingGLSecondCountable signedCompactPairingLocalField signedCompactPairingMeasurableSpace signedCompactPairingNBorelSpace signedCompactPairingNLocallyCompact signedCompactPairingNMeasurableSpace signedCompactPairingNSecondCountable signedCompactPairingT2 signedCompactPairingTopology signedCompactPairingTotallyDisconnected signedCompactPairingValuativeRel signedFourierOrbitOfCompact signedFourierOrbitOfCompact_left signedFourierOrbitOfCompact_locallyConstant signedMatrixOrbit signedMatrixOrbit_left signedOrbitBorelSpace signedOrbitGLSecondCountable signedOrbitLocalField signedOrbitMeasurableSpace signedOrbitNBorelSpace signedOrbitNLocallyCompact signedOrbitNMeasurableSpace signedOrbitNSecondCountable signedOrbitSecondCountable signedOrbitT2 signedOrbitTopology signedOrbitTotallyDisconnected signedOrbitValuativeRel signedSmoothLocalField signedSmoothNBorel signedSmoothNLocallyCompact signedSmoothNMeasurable signedSmoothTopology signedSmoothValuativeRel signedUnipotentMatrixFourier_exchange supportedSynthesisLocalField supportedSynthesisNBorel supportedSynthesisNMeasurable supportedSynthesisT2 supportedSynthesisTopology supportedSynthesisValuativeRel weightedCompactMatrixLift weightedCompactMatrixLift_orbit weightedCompactMatrixLift_support weightedSignedMatrixOrbit weightedSignedMatrixOrbitSmooth weightedSignedMatrixOrbitSmooth_eval weightedSignedMatrixOrbit_left weightedSignedMatrixOrbit_locallyConstant
open Langlands.AllField.RankinSelberg.CompactWhittakerSynthesis
open Langlands.RankinSelberg.CompactWhittakerApproximation hiding modelApproximationGLBorel modelApproximationGLLocallyCompact modelApproximationGLMeasurable modelApproximationGLNonarchimedean modelApproximationGLSigmaCompact modelApproximationLocalField modelApproximationT2 modelApproximationTopology modelApproximationValuativeRel weighted_glModel_integral_eq_of_compact
open Langlands.AllField.RankinSelberg.CompactWhittakerApproximation
open scoped NNReal ENNReal

universe uF uV
variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance principalModelDualT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance principalModelDualSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance principalModelDualMeasurable : MeasurableSpace F := borel _
local instance principalModelDualBorel : BorelSpace F := ⟨rfl⟩
local instance principalModelDualGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance principalModelDualGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance principalModelDualGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local instance principalModelDualTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The literal weighted signed-Weyl Fourier restriction of a group function. -/
def principalModelFourierIntegrand
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (m a : ℕ) (s : ℂ) (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (h : Langlands.GeneralLinear (m + 2) F) : ℂ :=
  let q := (⟨⟩ : LocalFieldData F).additiveConductor ψ
  let Ψ := boxLatticeTest F (n := m + 1) (q + a) q a
  (determinantWeight abv h s * W h) *
    rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl (m + 1) * h).val

/-- The true weighted block restriction, retaining the principal parameter. -/
def principalModelBlockIntegrand (m : ℕ) (s : ℂ)
    (W : Langlands.GeneralLinear (m + 2) F → ℂ)
    (z : Langlands.GeneralLinear (m + 2) F ×
      (Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F)) : ℂ :=
  determinantWeight abv z.2.1 s * W (principalSignedBlockPoint F m z.1 z.2)

private theorem continuous_principalModel_appendIdentity (n d : ℕ) :
    Continuous (appendIdentity (F := F) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (rankInclusionContinuous 1).continuous.comp ih

/-- Continuity of the literal block evaluation map gives its required
measurability without any quotient or orbit identification. -/
theorem continuous_principalSignedBlockPoint (m : ℕ) :
    Continuous (fun z : Langlands.GeneralLinear (m + 2) F ×
      (Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F) =>
      principalSignedBlockPoint F m z.1 z.2) := by
  have hgen (n r j k : ℕ) (hr : r = n + (j + k + 1)) :
      Continuous (fun z : Langlands.GeneralLinear (n + 1) F ×
        Matrix (Fin j) (Fin (n + 1)) F =>
        AdjacentBlockReduction.blockMatrixAt j k hr z.1 z.2) := by
    subst r
    change Continuous (fun z : Langlands.GeneralLinear (n + 1) F ×
      Matrix (Fin j) (Fin (n + 1)) F => unequalRankMatrix j k z.1 z.2)
    exact ((continuous_principalModel_appendIdentity F n (j + k + 1)).comp continuous_fst).mul
      ((continuous_rectangularUnipotent j k).comp continuous_snd)
  have hb := hgen 0 (m + 1) m 0 (by omega)
  exact ((hb.comp continuous_snd).mul_const _).mul
    ((continuous_inverseTranspose _ _).comp continuous_fst)

/-- The compact distribution identity extends to every actual smooth
coefficient-model vector when its two genuine weighted restrictions converge.
No gamma equation or original irreducibility is used. -/
theorem principalModelDual_pairing
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) {m a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ (⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 2) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ (m + 1) σ)
    (f : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule) (s : ℂ)
    (hi : Integrable (principalModelFourierIntegrand F ψ ν m a s
        (glModelFunction ψ (m + 1) σ ℓ f)) (generalLinearHaar F (m + 1)))
    (hj : Integrable (principalModelBlockIntegrand F m s
        (glModelFunction ψ (m + 1) σ ℓ f))
      ((principalAveragingMeasure F (n := m + 1) a
        (boxExtractionConstant F (n := m + 1)
          ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
          ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a)).prod
        ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)))) :
    (∫ h, principalModelFourierIntegrand F ψ ν m a s
      (glModelFunction ψ (m + 1) σ ℓ f) h ∂generalLinearHaar F (m + 1)) =
    ∫ z, principalModelBlockIntegrand F m s (glModelFunction ψ (m + 1) σ ℓ f) z
      ∂(principalAveragingMeasure F (n := m + 1) a
        (boxExtractionConstant F (n := m + 1)
          ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
          ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a)).prod
        ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) := by
  let q := (⟨⟩ : LocalFieldData F).additiveConductor ψ
  let Ψ := boxLatticeTest F (n := m + 1) (q + a) q a
  let C := boxExtractionConstant F (n := m + 1) (q + a) q a
  let μ := principalAveragingMeasure F (n := m + 1) a C
  let L := fun h : Langlands.GeneralLinear (m + 2) F =>
    determinantWeight abv h s * rectangularFourierIntegral ψ ν Ψ
      (rankOneSignedWeyl (m + 1) * h).val
  let R := fun z : Langlands.GeneralLinear (m + 2) F ×
      (Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F) =>
    determinantWeight abv z.2.1 s
  have hc (g : CompactFunctions (upperUnipotent (m + 2) F)
      (characterRepresentation (standardCharacter ψ (m + 1)))) :
      (∫ h : Langlands.GeneralLinear (m + 2) F,
        L h * eval _ _ g.val h ∂generalLinearHaar F (m + 1)) =
      ∫ z, R z * eval _ _ g.val (principalSignedBlockPoint F m z.1 z.2)
        ∂μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) := by
    have h := (principalCompactDual_pairing_weighted F ψ ν hsd ha hA g s).2.2
    simpa only [L, R, principalCompactDualIntegrand, mul_right_comm] using h
  have hpoint (h : Langlands.GeneralLinear (m + 2) F) :
      L h * glModelFunction ψ (m + 1) σ ℓ f h =
        principalModelFourierIntegrand F ψ ν m a s (glModelFunction ψ (m + 1) σ ℓ f) h := by
    simp only [L, principalModelFourierIntegrand, Ψ, q, mul_right_comm]
  have hi' : Integrable (fun h : Langlands.GeneralLinear (m + 2) F =>
      L h * glModelFunction ψ (m + 1) σ ℓ f h)
      (generalLinearHaar F (m + 1)) :=
    hi.congr (g := fun h => L h * glModelFunction ψ (m + 1) σ ℓ f h)
      (Filter.Eventually.of_forall fun h => (hpoint h).symm)
  have hj' : Integrable (fun z => R z * glModelFunction ψ (m + 1) σ ℓ f
      (principalSignedBlockPoint F m z.1 z.2))
      (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) := hj
  have he := weighted_glModel_integral_eq_of_compact F ψ (m + 1) σ hσ ℓ
    (generalLinearHaar F (m + 1))
    (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)))
    id (fun z => principalSignedBlockPoint F m z.1 z.2) L R measurable_id
    (continuous_principalSignedBlockPoint F m).measurable hc f hi' hj'
  exact (integral_congr_ae (Filter.Eventually.of_forall fun h => (hpoint h).symm)).trans he

end Langlands.AllField.RankinSelberg
