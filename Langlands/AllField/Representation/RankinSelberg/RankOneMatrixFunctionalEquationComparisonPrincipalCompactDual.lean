import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalCompactDual
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonCompactGLParameters
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalWeighted
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedCompactPairing
/-! Compact principal extraction of the actual signed complementary block. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement compactParametersBorel compactParametersGLBorel compactParametersGLLocallyCompact compactParametersGLMeasurable compactParametersGLSecondCountable compactParametersLocalField compactParametersMeasurable compactParametersNBorel compactParametersNMeasurable compactParametersSecondCountable compactParametersT2 compactParametersTopology compactParametersTotallyDisconnected compactParametersValuativeRel determinantNorm_rankOneSignedBlockWeyl determinantWeight_principalSignedBlockPoint diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType glOneWeight_eq_determinantWeight glOneWeight_smul_natSucc integrable_generalLinear_one_natWeight_iff integrable_generalLinear_one_prod_natWeight_iff integrable_prod_generalLinear_one_natWeight_iff integral_generalLinear_one_natWeight integral_generalLinear_one_prod_natWeight integral_prod_generalLinear_one_natWeight isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow orbitBlocksBorel orbitBlocksLocalField orbitBlocksMeasurable orbitBlocksNBorel orbitBlocksNLocallyCompact orbitBlocksNMeasurable orbitBlocksNSecondCountable orbitBlocksSecondCountable orbitBlocksSigmaCompact orbitBlocksT2 orbitBlocksTopology orbitBlocksTotallyDisconnected orbitBlocksValuativeRel padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType parameter_glOneMeasure_block_density parameter_glOneMeasure_density principalCompactDualBorel principalCompactDualGLBorel principalCompactDualGLMeasurable principalCompactDualGLSecondCountable principalCompactDualIntegrand principalCompactDualIntegrand_reconstruct principalCompactDualLocalField principalCompactDualMeasurable principalCompactDualSecondCountable principalCompactDualT2 principalCompactDualTopology principalCompactDualTotallyDisconnected principalCompactDualUnitsBorel principalCompactDualUnitsMeasurable principalCompactDualUnitsSecondCountable principalCompactDualValuativeRel principalCompactDual_fourierOrbit_duality principalCompactDual_pairing principalCompactDual_pairing_weighted principalCompactFourier_reconstruct principalCompactKernel principalCompactKernel_ae principalCompactKernel_detNorm principalCompactKernel_of_mem principalSignedBlockPoint rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero scalarHaarBorel scalarHaarGLBorel scalarHaarGLLocallyCompact scalarHaarGLMeasurable scalarHaarGLSecondCountable scalarHaarLocalField scalarHaarMeasurable scalarHaarNullSingleton scalarHaarSecondCountable scalarHaarSigmaCompact scalarHaarT2 scalarHaarTopology scalarHaarValuativeRel signedBlockGLParameterIntegrand signedWeylGLParameterIntegrand signedWeylGL_blockGL_parameter_duality signedWeylOrbit_blockOrbit_fourier_duality signedWeylOrbit_blockOrbit_fourier_duality_averaged signedWeyl_affineBlock_fourier_duality singleton_modulus_real tsupport_boxLatticeTest_subset unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan weylBlockBorelSpace weylBlockLocalField weylBlockMeasurableSpace weylBlockNBorelSpace weylBlockNLocallyCompact weylBlockNMeasurableSpace weylBlockNSecondCountable weylBlockSecondCountable weylBlockSigmaCompact weylBlockT2 weylBlockTopology weylBlockTotallyDisconnected weylBlockValuativeRel zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
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
open Langlands.Conductor
open scoped NNReal ENNReal

universe uF uX
variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance principalCompactDualT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance principalCompactDualSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance principalCompactDualMeasurable : MeasurableSpace F := borel _
local instance principalCompactDualBorel : BorelSpace F := ⟨rfl⟩
local instance principalCompactDualGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance principalCompactDualGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance principalCompactDualGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)
local instance principalCompactDualTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local instance principalCompactDualUnitsMeasurable : MeasurableSpace Fˣ := borel _
local instance principalCompactDualUnitsBorel : BorelSpace Fˣ := ⟨rfl⟩
local instance principalCompactDualUnitsSecondCountable : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The compact principal subgroup indicator is retained until convergence
has been proved on the full product. -/
def principalCompactKernel (n a : ℕ) :
    SchwartzBruhat (Langlands.GeneralLinear (n + 1) F) :=
  ⟨(principalLevelOpenSubgroup F n a :
        Set (Langlands.GeneralLinear (n + 1) F)).indicator (fun _ => (1 : ℂ)),
    by
      classical
      let S := (principalLevelOpenSubgroup F n a :
        Set (Langlands.GeneralLinear (n + 1) F))
      have hs : IsClopen S := (principalLevelOpenSubgroup F n a).isClopen
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
      by_cases hx : x ∈ S
      · filter_upwards [hs.isOpen.mem_nhds hx] with y hy
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
      · filter_upwards [hs.isClosed.isOpen_compl.mem_nhds hx] with y hy
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx],
    HasCompactSupport.intro (isCompact_principalLevelOpenSubgroup F n a)
      (fun _ hx => Set.indicator_of_notMem hx _)⟩

@[simp] theorem principalCompactKernel_of_mem (n a : ℕ)
    {k : Langlands.GeneralLinear (n + 1) F}
    (hk : k ∈ principalLevelSubgroup F n a) :
    principalCompactKernel F n a k = 1 := by
  change (principalLevelOpenSubgroup F n a :
        Set (Langlands.GeneralLinear (n + 1) F)).indicator
    (fun _ => (1 : ℂ)) k = 1
  exact Set.indicator_of_mem hk _

theorem principalCompactKernel_ae (n a : ℕ) (C : ℝ) :
    ∀ᵐ k ∂principalAveragingMeasure F (n := n) a C,
      principalCompactKernel F n a k = 1 := by
  filter_upwards [principalAveragingMeasure_ae_mem F a C] with k hk
  exact principalCompactKernel_of_mem F n a hk

theorem principalCompactKernel_detNorm (n a : ℕ)
    (k : Langlands.GeneralLinear (n + 1) F)
    (hk : principalCompactKernel F n a k ≠ 0) :
    (⟨⟩ : LocalFieldData F).determinantNorm (n + 1) k = 1 := by
  have hmem : k ∈ principalLevelSubgroup F n a := by
    by_contra hn
    apply hk
    change (principalLevelOpenSubgroup F n a :
        Set (Langlands.GeneralLinear (n + 1) F)).indicator
      (fun _ => (1 : ℂ)) k = 0
    exact Set.indicator_of_notMem hn _
  apply Units.ext
  apply NNReal.eq
  have h := abv_det_eq_one F (principalLevel_le_integral F a hmem)
  exact h

/-- The literal complementary-block evaluation point, with its actual signed
block Weyl factor and inverse transpose of the averaging parameter. -/
def principalSignedBlockPoint (m : ℕ)
    (k : Langlands.GeneralLinear (m + 2) F)
    (z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F) :
    Langlands.GeneralLinear (m + 2) F :=
  AdjacentBlockReduction.blockMatrixAt m 0 (by omega) z.1 z.2 *
    rankOneSignedBlockWeyl (m + 1) (by omega) *
    inverseTranspose (m + 2) F k

/-- The actual principal compact dual block restriction, before averaging. -/
def principalCompactDualIntegrand (ψ : UnitaryAdditiveCharacter F)
    (m : ℕ)
    (f : CompactFunctions (upperUnipotent (m + 2) F)
      (characterRepresentation (standardCharacter ψ (m + 1))))
    (z : Langlands.GeneralLinear (m + 2) F ×
      (Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F)) : ℂ :=
  eval _ _ f.val (principalSignedBlockPoint F m z.1 z.2)

/-- The real GL1 density is the corresponding complex determinant power. -/
theorem glOneWeight_eq_determinantWeight (n : ℕ)
    (g : Langlands.GeneralLinear 1 F) :
    ((weight F n (g, 1) : ℝ) : ℂ) = determinantWeight abv g (-(n : ℂ)) := by
  rw [weight_glOne]
  simp only [determinantWeight, Complex.cpow_neg, Complex.cpow_natCast,
    NNReal.coe_inv, NNReal.coe_pow, Complex.ofReal_inv, Complex.ofReal_pow,
    (⟨⟩ : LocalFieldData F).normalizedAbsUnits_coe,
    Matrix.GeneralLinearGroup.val_det_apply, normalizedAbsoluteValue_apply]

/-- Natural ambient weight and the GL1 density leave exponent one. -/
theorem glOneWeight_smul_natSucc (n : ℕ)
    (g : Langlands.GeneralLinear 1 F) (z : ℂ) :
    weight F n (g, 1) • (determinantWeight abv g (n + 1 : ℕ) * z) =
      determinantWeight abv g 1 * z := by
  rw [NNReal.smul_def, Complex.real_smul, glOneWeight_eq_determinantWeight,
    ← mul_assoc]
  have hg : determinantWeight abv g (-(n : ℂ)) *
      determinantWeight abv g (n + 1 : ℕ) = determinantWeight abv g 1 := by
    unfold determinantWeight
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).ne_zero
        (Matrix.GeneralLinearGroup.det_ne_zero g)))]
    congr 1
    push_cast
    ring
  rw [hg]

/-- The block restriction preserves the scalar determinant norm when the
principal averaging parameter has norm one. -/
theorem determinantWeight_principalSignedBlockPoint (m : ℕ)
    (k : Langlands.GeneralLinear (m + 2) F)
    (hk : (⟨⟩ : LocalFieldData F).determinantNorm (m + 2) k = 1)
    (z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F)
    (s : ℂ) :
    determinantWeight abv (principalSignedBlockPoint F m k z) s =
      determinantWeight abv z.1 s := by
  have hB : abv (Matrix.det (rankOneSignedBlockWeyl (m + 1)
      (K := F) (by omega)).val) = 1 := by
    have hb := determinantNorm_rankOneSignedBlockWeyl F (m + 1) (by omega)
    have hb' := congrArg (fun t : ℝ≥0ˣ => ((t : ℝ≥0) : ℝ)) hb
    exact hb'
  have hki : abv (Matrix.det (inverseTranspose (m + 2) F k).val) = 1 := by
    have hk' : (⟨⟩ : LocalFieldData F).determinantNorm (m + 2)
        (inverseTranspose (m + 2) F k) = 1 := by
      rw [(⟨⟩ : LocalFieldData F).determinantNorm_inverseTranspose, hk, inv_one]
    exact congrArg (fun t : ℝ≥0ˣ => ((t : ℝ≥0) : ℝ)) hk'
  have hd : Matrix.det (AdjacentBlockReduction.blockMatrixAt (n := 0) (r := m + 1) m 0
      (by omega) z.1 z.2).val = Matrix.det z.1.val := by
    rw [← firstColumnMatrix_eq_blockMatrixAt, det_firstColumnMatrix]
    simp only [rankOneAffineParameters_zero, Matrix.det_fin_one]
  simp only [principalSignedBlockPoint, determinantWeight, Units.val_mul,
    Matrix.det_mul, map_mul, hB, hki, hd, mul_one]

/-- Reconstruction is pointwise; its full-product use below is justified by
the previously proved parameter convergence. -/
theorem principalCompactDualIntegrand_reconstruct
    (ψ : UnitaryAdditiveCharacter F) (m a : ℕ)
    (f : CompactFunctions (upperUnipotent (m + 2) F)
      (characterRepresentation (standardCharacter ψ (m + 1))))
    (k : Langlands.GeneralLinear (m + 2) F)
    (hk : (⟨⟩ : LocalFieldData F).determinantNorm (m + 2) k = 1)
    (hκ : principalCompactKernel F (m + 1) a k = 1)
    (z : Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F) :
    weight F (m + 1) (z.1, 1) • principalCompactDualIntegrand F ψ m f (k, z) =
      signedBlockGLParameterIntegrand F ψ m id (principalCompactKernel F (m + 1) a)
        (weightedCompactMatrixLift F ψ (m + 1) (m + 2 : ℕ) f) (k, z) := by
  have he := weightedCompactMatrixLift_orbit F ψ (m + 1) (m + 2 : ℕ) f
    (principalSignedBlockPoint F m k z)
  rw [determinantWeight_principalSignedBlockPoint F m k hk] at he
  change weight F (m + 1) (z.1, 1) •
    eval _ _ f.val (principalSignedBlockPoint F m k z) = _
  rw [← he, glOneWeight_smul_natSucc]
  simp only [signedBlockGLParameterIntegrand, hκ, one_mul, id_eq,
    signedBlockOrbitKernel_at_generalLinear, principalSignedBlockPoint, mul_assoc]

/-- The natural scalar Fourier orbit has exactly the density used by the
joint Fourier/block identity. -/
theorem principalCompactFourier_reconstruct
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (m a : ℕ)
    (f : CompactFunctions (upperUnipotent (m + 2) F)
      (characterRepresentation (standardCharacter ψ (m + 1))))
    (k : Langlands.GeneralLinear (m + 2) F)
    (hk : (⟨⟩ : LocalFieldData F).determinantNorm (m + 2) k = 1)
    (hκ : principalCompactKernel F (m + 1) a k = 1)
    (g : Langlands.GeneralLinear 1 F) :
    weight F (m + 1) (g, 1) •
      signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f (rankOneEmbedding m g * k) =
      signedWeylGLParameterIntegrand F ψ ν m id (principalCompactKernel F (m + 1) a)
        (weightedCompactMatrixLift F ψ (m + 1) (m + 2 : ℕ) f) (k, g) := by
  have hknorm : abv (Matrix.det k.val) = 1 :=
    congrArg (fun t : ℝ≥0ˣ => ((t : ℝ≥0) : ℝ)) hk
  unfold signedFourierOrbitOfCompact weightedSignedMatrixOrbit
  rw [determinantWeight_mul_of_norm_one F _ k hknorm,
    determinantWeight_rankOneEmbedding, glOneWeight_smul_natSucc]
  simp only [signedMatrixOrbit, signedWeylGLParameterIntegrand,
    signedWeylOrbitFourierKernel, rectangularFourierEquiv_apply,
    hκ, one_mul, id_eq, Units.val_mul, rankOneEmbedding_val, Matrix.mul_assoc]

private theorem measurable_glOneWeight (n : ℕ) :
    Measurable (fun g : Langlands.GeneralLinear 1 F => weight F n (g, 1)) :=
  (continuous_weight F n).measurable.comp (measurable_id.prodMk measurable_const)

/-- Retaining a parameter commutes with passing to the actual weighted
GL1 measure. -/
theorem parameter_glOneMeasure_density {X : Type uX} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (n : ℕ) :
    μ.prod (glOneMeasure F n) =
      (μ.prod (generalLinearHaar F 0)).withDensity
        (fun z => (weight F n (z.2, 1) : ℝ≥0∞)) := by
  exact prod_withDensity_right
    (measurable_glOneWeight F n).coe_nnreal_ennreal

/-- Both the compact parameter and the complementary block commute with
the true weighted GL1 measure, before any averaging. -/
theorem parameter_glOneMeasure_block_density {X : Type uX} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (ν : AdditiveHaarMeasure F) (m : ℕ) :
    μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) =
      (μ.prod ((generalLinearHaar F 0).prod (rectangularMeasure ν m 1))).withDensity
        (fun z => (weight F (m + 1) (z.2.1, 1) : ℝ≥0∞)) := by
  unfold glOneMeasure
  rw [prod_withDensity_left
    (measurable_glOneWeight F (m + 1)).coe_nnreal_ennreal]
  exact prod_withDensity_right
    ((measurable_glOneWeight F (m + 1)).coe_nnreal_ennreal.comp measurable_fst)

/-- The compact principal parameter remains in the full complementary-block
integral: no cancellation inside its average is used for convergence. -/
theorem principalCompactDual_fourierOrbit_duality
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (m a : ℕ) (C : ℝ)
    (f : CompactFunctions (upperUnipotent (m + 2) F)
      (characterRepresentation (standardCharacter ψ (m + 1)))) :
    let μ := principalAveragingMeasure F (n := m + 1) a C
    Integrable (fun z : Langlands.GeneralLinear (m + 2) F ×
        Langlands.GeneralLinear 1 F =>
      signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f (rankOneEmbedding m z.2 * z.1))
      (μ.prod (glOneMeasure F (m + 1))) ∧
    Integrable (principalCompactDualIntegrand F ψ m f)
      (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) ∧
    (∫ z : Langlands.GeneralLinear (m + 2) F × Langlands.GeneralLinear 1 F,
      signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f (rankOneEmbedding m z.2 * z.1)
      ∂μ.prod (glOneMeasure F (m + 1))) =
    ∫ z, principalCompactDualIntegrand F ψ m f z
      ∂μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) := by
  dsimp only
  let μ := principalAveragingMeasure F (n := m + 1) a C
  let Φ := weightedCompactMatrixLift F ψ (m + 1) (m + 2 : ℕ) f
  let κ := principalCompactKernel F (m + 1) a
  let L := fun z : Langlands.GeneralLinear (m + 2) F ×
      Langlands.GeneralLinear 1 F =>
    signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f (rankOneEmbedding m z.2 * z.1)
  obtain ⟨hl, hr, he⟩ := signedWeylGL_blockGL_parameter_duality F μ ψ ν hsd m
    id continuous_id κ (principalCompactKernel_detNorm F (m + 1) a) Φ
  have hwL : Measurable (fun z : Langlands.GeneralLinear (m + 2) F ×
      Langlands.GeneralLinear 1 F => weight F (m + 1) (z.2, 1)) :=
    (measurable_glOneWeight F (m + 1)).comp measurable_snd
  have hwR : Measurable (fun z : Langlands.GeneralLinear (m + 2) F ×
      (Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F) =>
      weight F (m + 1) (z.2.1, 1)) :=
    (measurable_glOneWeight F (m + 1)).comp (measurable_fst.comp measurable_snd)
  have hlae : (fun z : Langlands.GeneralLinear (m + 2) F ×
      Langlands.GeneralLinear 1 F => weight F (m + 1) (z.2, 1) • L z)
      =ᵐ[μ.prod (generalLinearHaar F 0)]
        signedWeylGLParameterIntegrand F ψ ν m id κ Φ := by
    have hκ := (Measure.quasiMeasurePreserving_fst
      (μ := μ) (ν := generalLinearHaar F 0)).ae
      (principalCompactKernel_ae F (m + 1) a C)
    have hk := (Measure.quasiMeasurePreserving_fst
      (μ := μ) (ν := generalLinearHaar F 0)).ae
      (principalAveragingMeasure_ae_det_norm F a C)
    filter_upwards [hκ, hk] with z hκ hk
    exact principalCompactFourier_reconstruct F ψ ν hsd m a f z.1
      (by apply Units.ext; apply NNReal.eq; exact hk) hκ z.2
  have hrae : (fun z : Langlands.GeneralLinear (m + 2) F ×
      (Langlands.GeneralLinear 1 F × Matrix (Fin m) (Fin 1) F) =>
      weight F (m + 1) (z.2.1, 1) • principalCompactDualIntegrand F ψ m f z)
      =ᵐ[μ.prod ((generalLinearHaar F 0).prod (rectangularMeasure ν m 1))]
        signedBlockGLParameterIntegrand F ψ m id κ Φ := by
    have hκ := (Measure.quasiMeasurePreserving_fst
      (μ := μ) (ν := (generalLinearHaar F 0).prod (rectangularMeasure ν m 1))).ae
      (principalCompactKernel_ae F (m + 1) a C)
    have hk := (Measure.quasiMeasurePreserving_fst
      (μ := μ) (ν := (generalLinearHaar F 0).prod (rectangularMeasure ν m 1))).ae
      (principalAveragingMeasure_ae_det_norm F a C)
    filter_upwards [hκ, hk] with z hκ hk
    exact principalCompactDualIntegrand_reconstruct F ψ m a f z.1
      (by apply Units.ext; apply NNReal.eq; exact hk) hκ z.2
  have hl' : Integrable L (μ.prod (glOneMeasure F (m + 1))) := by
    rw [parameter_glOneMeasure_density,
      integrable_withDensity_iff_integrable_smul hwL]
    exact hl.congr hlae.symm
  have hr' : Integrable (principalCompactDualIntegrand F ψ m f)
      (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) := by
    rw [parameter_glOneMeasure_block_density,
      integrable_withDensity_iff_integrable_smul hwR]
    exact hr.congr hrae.symm
  refine ⟨hl', hr', ?_⟩
  change (∫ z, L z ∂μ.prod (glOneMeasure F (m + 1))) = _
  rw [parameter_glOneMeasure_density,
    integral_withDensity_eq_integral_smul hwL,
    integral_congr_ae hlae, he,
    parameter_glOneMeasure_block_density,
    integral_withDensity_eq_integral_smul hwR]
  exact integral_congr_ae hrae.symm

/-- The fixed lattice test is supported in its actual compact open box. -/
theorem tsupport_boxLatticeTest_subset (n : ℕ) (A q : ℤ) (a : ℕ) :
    tsupport (boxLatticeTest F (n := n) A q a : _ → ℂ) ⊆ box F A q a := by
  apply closure_minimal _ (isCompact_box F A q a).isClosed
  intro X hX
  by_contra hn
  apply hX
  rw [boxLatticeTest_apply, Set.indicator_of_notMem hn]

/-- One original box test and its same principal measure give the actual
signed complementary block identity for every compact Whittaker input, with
both full product convergence and no additional scalar. -/
theorem principalCompactDual_pairing
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) {m a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ (⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    (f : CompactFunctions (upperUnipotent (m + 2) F)
      (characterRepresentation (standardCharacter ψ (m + 1)))) :
    let q := (⟨⟩ : LocalFieldData F).additiveConductor ψ
    let Ψ := boxLatticeTest F (n := m + 1) (q + a) q a
    let C := boxExtractionConstant F (n := m + 1) (q + a) q a
    let μ := principalAveragingMeasure F (n := m + 1) a C
    Integrable (fun h : Langlands.GeneralLinear (m + 2) F =>
      eval _ _ f.val h * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl (m + 1) * h).val)
      (generalLinearHaar F (m + 1)) ∧
    Integrable (principalCompactDualIntegrand F ψ m f)
      (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) ∧
    (∫ h : Langlands.GeneralLinear (m + 2) F,
      eval _ _ f.val h * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl (m + 1) * h).val
      ∂generalLinearHaar F (m + 1)) =
    ∫ z, principalCompactDualIntegrand F ψ m f z
      ∂μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) := by
  dsimp only
  let q := (⟨⟩ : LocalFieldData F).additiveConductor ψ
  let Ψ := boxLatticeTest F (n := m + 1) (q + a) q a
  let C := boxExtractionConstant F (n := m + 1) (q + a) q a
  let μ := principalAveragingMeasure F (n := m + 1) a C
  let K := signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f
  obtain ⟨hK, hf, hp⟩ := compact_signedFourier_pairing F ψ ν hsd (m + 1) f Ψ
    (q + a) q ha (tsupport_boxLatticeTest_subset F (m + 1) (q + a) q a)
  have hK' : Integrable (fun h : Langlands.GeneralLinear (m + 2) F =>
      Ψ h.val * K h) (generalLinearHaar F (m + 1)) :=
    hK.congr (g := fun h => Ψ h.val * K h)
      (Filter.Eventually.of_forall fun h => mul_comm (K h) (Ψ h.val))
  obtain ⟨_, hx⟩ := principalMeasure_extraction F ψ ha hA K
    (continuous_signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f)
    (signedFourierOrbitOfCompact_left F ψ ν hsd (m + 1) f) hK'
  obtain ⟨hl, hr, he⟩ := principalCompactDual_fourierOrbit_duality F ψ ν hsd m a C f
  refine ⟨hf, hr, ?_⟩
  calc
    _ = ∫ h, K h * Ψ h.val ∂generalLinearHaar F (m + 1) := by
      exact hp.symm
    _ = ∫ h, Ψ h.val * K h ∂generalLinearHaar F (m + 1) :=
      integral_congr_ae (Filter.Eventually.of_forall fun h => mul_comm (K h) (Ψ h.val))
    _ = ∫ g, ∫ k, K (rankOneEmbedding m g * k) ∂μ ∂glOneMeasure F (m + 1) := hx
    _ = ∫ z, K (rankOneEmbedding m z.2 * z.1) ∂μ.prod (glOneMeasure F (m + 1)) :=
      (integral_prod_symm _ hl).symm
    _ = _ := he

/-- Determinant twisting takes place on the actual compact group function.
The same original box and same principal measure work for every complex
spectral exponent, with genuine full product convergence. -/
theorem principalCompactDual_pairing_weighted
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) {m a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ (⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    (f : CompactFunctions (upperUnipotent (m + 2) F)
      (characterRepresentation (standardCharacter ψ (m + 1)))) (s : ℂ) :
    let q := (⟨⟩ : LocalFieldData F).additiveConductor ψ
    let Ψ := boxLatticeTest F (n := m + 1) (q + a) q a
    let C := boxExtractionConstant F (n := m + 1) (q + a) q a
    let μ := principalAveragingMeasure F (n := m + 1) a C
    Integrable (fun h : Langlands.GeneralLinear (m + 2) F =>
      (determinantWeight abv h s * eval _ _ f.val h) *
        rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl (m + 1) * h).val)
      (generalLinearHaar F (m + 1)) ∧
    Integrable (fun z => determinantWeight abv z.2.1 s * principalCompactDualIntegrand F ψ m f z)
      (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) ∧
    (∫ h : Langlands.GeneralLinear (m + 2) F,
      (determinantWeight abv h s * eval _ _ f.val h) *
        rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl (m + 1) * h).val
      ∂generalLinearHaar F (m + 1)) =
    ∫ z, determinantWeight abv z.2.1 s * principalCompactDualIntegrand F ψ m f z
      ∂μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) := by
  dsimp only
  let C := boxExtractionConstant F (n := m + 1)
    ((⟨⟩ : LocalFieldData F).additiveConductor ψ + a)
    ((⟨⟩ : LocalFieldData F).additiveConductor ψ) a
  let μ := principalAveragingMeasure F (n := m + 1) a C
  let f' := weightedCompactFunction abv
    (Langlands.LocalFieldData.isOpenNormOne_of_eq_normalizedAbs (T := ⟨⟩) (fun _ => rfl))
    (m + 1) (standardCharacter ψ (m + 1)) (-s) f
  obtain ⟨hi, hj, he⟩ := principalCompactDual_pairing F ψ ν hsd ha hA f'
  have hae : principalCompactDualIntegrand F ψ m f'
      =ᵐ[μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))]
        (fun z => determinantWeight abv z.2.1 s * principalCompactDualIntegrand F ψ m f z) := by
    have hk := (Measure.quasiMeasurePreserving_fst (μ := μ)
      (ν := (glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))).ae
      (principalAveragingMeasure_ae_det_norm F a C)
    filter_upwards [hk] with z hz
    simp only [principalCompactDualIntegrand, f', weightedCompactFunction_apply, neg_neg]
    rw [determinantWeight_principalSignedBlockPoint F m z.1
      (by apply Units.ext; apply NNReal.eq; exact hz)]
  refine ⟨?_, hj.congr hae, ?_⟩
  · simpa only [f', weightedCompactFunction_apply, neg_neg] using hi
  · simpa only [f', weightedCompactFunction_apply, neg_neg] using
      he.trans (integral_congr_ae hae)

end Langlands.AllField.RankinSelberg
