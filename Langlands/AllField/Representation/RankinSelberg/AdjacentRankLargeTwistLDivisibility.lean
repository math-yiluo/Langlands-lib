import Langlands.Representation.RankinSelberg.AdjacentRankLargeTwistLDivisibility
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankImageLDivisibility
import Langlands.AllField.Representation.RankinSelberg.CanonicalPairLFactor
/-! Certified polynomial divisibility for the actual large-second-twist lower induction. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankCoefficientConvolution AdjacentRankCorankDenominatorBound AdjacentRankInvariantApproximationData AdjacentRankLargeTwistLDivisibility AdjacentRankModelConverges AdjacentRankModelCorankDenominatorBound AdjacentRankProductContinuationData AdjacentRankShellConvolutionAt AdjacentRankShellLowerBounds adjacentAdmissibilityLocalField adjacentAdmissibilityTopology adjacentAdmissibilityValuativeRel adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCoefficientConvolution_of_shell adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualInnerSliceIntegral adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankFiniteProductValue adjacentRankImage_productDenominatorBound adjacentRankInducedModelBound adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankInvariantApproximation adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankLargeTwistLDivisibility adjacentRankLowerCompactRepresentation adjacentRankLowerInducingCoordinates adjacentRankLowerTensorCoordinates_action adjacentRankLowerTensorRepresentation adjacentRankLowerTensorRepresentation_isAdmissible adjacentRankMatrixSliceCoefficient adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound adjacentRankMatrixSliceExpansion adjacentRankModelBound_polynomialDivisibility adjacentRankModelConverges_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegral_mul adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModelMap adjacentRankModelMapBorel adjacentRankModelMapDisconnected adjacentRankModelMapGLMeasurable adjacentRankModelMapLocalField adjacentRankModelMapMeasurable adjacentRankModelMapT2 adjacentRankModelMapTopology adjacentRankModelMapValuative adjacentRankModelMap_apply adjacentRankModelStarScalar adjacentRankModelStar_corankOneSlice_eq_before adjacentRankModelStar_separated_rankInclusion adjacentRankModelStar_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankModel_matchedCoefficientConvolution adjacentRankModel_matchedProductContinuation adjacentRankModel_matchedProductContinuation_exists adjacentRankNormalizedInduced_isAdmissible adjacentRankNormalizedOpposite_isOfWhittakerType adjacentRankNormalizedSection adjacentRankNormalizedSectionTensor adjacentRankNormalizedSectionTensor_surjective adjacentRankNormalizedSectionTensor_tmul adjacentRankNormalizedSection_eval adjacentRankNormalizedSection_right adjacentRankProductContinuation_denominatorBound adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_finiteConvolution_of_innerSeparation adjacentRankShell_matchedFiniteConvolution adjacentRankShell_shear_fubini adjacentRankTest_exists_sum_separated adjacentSectionFieldTopology adjacentSectionGLBorel adjacentSectionGLMeasurable adjacentSectionLocalField adjacentSectionT2 adjacentSectionValuativeRel compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuationFieldMeasurableSpace continuationFieldTopology continuationFieldValuation continuationGroupBorelSpace continuationGroupMeasurableSpace continuationLocalField continuationQuotientMeasurableSpace continuationUnipotentBorelSpace continuationUnipotentMeasurableSpace continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel corankOneCoefficient_convergesOnRight corankOneCoefficient_productContinuation corankOneCoefficient_scalarProductContinuation corankOneIntegral_eq_finiteProducts_of_coefficients corankOneIntegral_eq_zeroZero corankOneIntegrand_eq_mul_spectralPoint_zpow corankOneSliceExpansion dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel dualModelFieldBorel dualModelFieldMeasurable dualModelFieldT2 dualModelFieldTopology dualModelFieldTotallyDisconnected dualModelGroupBorel dualModelGroupMeasurable dualModelLocalField dualModelValuativeRel dualRestrictionFieldBorel dualRestrictionFieldMeasurable dualRestrictionFieldT2 dualRestrictionFieldTopology dualRestrictionFieldTotallyDisconnected dualRestrictionGroupBorel dualRestrictionGroupMeasurable dualRestrictionLocalField dualRestrictionValuativeRel equalRankSliceCoefficient_eq_zero_of_pointwise_bound exists_adjacentRankInner_subgroup exists_adjacentRankModelMatrixValues exists_adjacentRankTestWeightLevel exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice hasSum_setIntegral_generalLinearDeterminantSlice imageBoundFieldBorel imageBoundFieldMeasurable imageBoundFieldT2 imageBoundFieldTotallyDisconnected imageBoundGroupBorel imageBoundGroupMeasurable imageBoundLocalField imageBoundQuotientMeasurable imageBoundTopology imageBoundUnipotentBorel imageBoundUnipotentMeasurable imageBoundValuativeRel inducedModelFieldBorel inducedModelFieldMeasurable inducedModelFieldT2 inducedModelFieldTotallyDisconnected inducedModelLocalField inducedModelTopology inducedModelValuativeRel innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices invariantApproximationGLLocallyCompact invariantApproximationGLNonarch invariantApproximationLocalField invariantApproximationNonarchRing invariantApproximationSecondCountable invariantApproximationT2 invariantApproximationTopology invariantApproximationValuativeRel inverseCoefficientAsScaledStandard isClopen_adjacentRankJointShell isPadicPairLPolynomial_characterChange isPadicSymmetricLPolynomial_characterChange isPadicSymmetricLPolynomial_comm jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel largeTwistLFieldBorel largeTwistLFieldMeasurable largeTwistLFieldT2 largeTwistLFieldTotallyDisconnected largeTwistLGroupBorel largeTwistLGroupMeasurable largeTwistLLocalField largeTwistLQuotientBorel largeTwistLQuotientMeasurable largeTwistLTopology largeTwistLUnipotentBorel largeTwistLUnipotentMeasurable largeTwistLValuativeRel matchedCoefficientFieldBorel matchedCoefficientFieldMeasurable matchedCoefficientFieldT2 matchedCoefficientFieldTopology matchedCoefficientFieldTotallyDisconnected matchedCoefficientGroupBorel matchedCoefficientGroupMeasurable matchedCoefficientGroupSigmaCompact matchedCoefficientLocalField matchedCoefficientQuotientBorel matchedCoefficientQuotientMeasurable matchedCoefficientUnipotentBorel matchedCoefficientUnipotentMeasurable matchedCoefficientValuativeRel matchedContinuationFieldBorel matchedContinuationFieldMeasurable matchedContinuationFieldT2 matchedContinuationFieldTopology matchedContinuationFieldTotallyDisconnected matchedContinuationGroupBorel matchedContinuationGroupMeasurable matchedContinuationLocalField matchedContinuationQuotientMeasurable matchedContinuationUnipotentBorel matchedContinuationUnipotentMeasurable matchedContinuationValuativeRel matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel matchedShellFieldT2 matchedShellFieldTopology matchedShellGroupBorel matchedShellGroupMeasurable matchedShellGroupSecondCountable matchedShellGroupSigmaCompact matchedShellLocalField matchedShellQuotientLocallyCompact matchedShellQuotientMeasurable matchedShellQuotientSecondCountable matchedShellUnipotentBorel matchedShellUnipotentMeasurable matchedShellValuativeRel matrixWitnessFieldBorel matrixWitnessFieldMeasurable matrixWitnessFieldT2 matrixWitnessFieldTotallyDisconnected matrixWitnessGroupBorel matrixWitnessGroupMeasurable matrixWitnessLocalField matrixWitnessQuotientMeasurable matrixWitnessTopology matrixWitnessUnipotentBorel matrixWitnessUnipotentMeasurable matrixWitnessValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel nonempty_adjacentRankInvariantApproximation oppositeParabolicQuotientCompact productBoundFieldMeasurable productBoundGroupBorel productBoundGroupMeasurable productBoundLocalField productBoundModelAddCommGroup productBoundQuotientMeasurable productBoundTopology productBoundUnipotentBorel productBoundUnipotentMeasurable productBoundValuativeRel productsFieldTopology productsQuotientMeasurableSpace quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel scaledStandardCoefficientAsInverse sectionSurjectivityGLBorel sectionSurjectivityGLMeasurable sectionSurjectivityLocalField sectionSurjectivityT2 sectionSurjectivityTopology sectionSurjectivityValuativeRel setIntegral_matrixIntegrand_determinantSlice shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel spectralFieldTopology spectralFieldValuation spectralGroupBorelSpace spectralGroupMeasurableSpace spectralLocalField spectralQuotientBorelSpace spectralQuotientMeasurableSpace
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelConverges AdjacentRankModelImageStatement AdjacentRankModelStarStatement CharacterChangeCompatibleMeasureStatement CharacterChangeRectangularHaarStatement CharacterChangeRectangularProductStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockJacquetConvergenceStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelImage adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankStarEquiv adjacentRankStarEquiv_tmul_evaluation adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus characterChangeRectangularHaarStatement characterChangeRectangularProductStatement continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_canonical isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist isPairLPolynomial_characterChange_canonical isUnequalRankLPolynomial_characterChange_canonical iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice symmetricLPolynomialExists twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockGammaRankOne_of_trivial_test twoBlockJacquetConvergence twoBlockLRankOne_of_trivial_test twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentQuotientHaar_characterChange unipotentQuotientHaar_sigmaFinite_normalized unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_canonical zetaSpan_equalRank_characterChange_normalized zetaSpan_unequalRank_characterChange_canonical
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement adjacentRankUnipotentFourier padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic exists_compactOpen_glCoefficientRightStabilizer functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance largeTwistLFieldT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance largeTwistLFieldTotallyDisconnected :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance largeTwistLFieldMeasurable : MeasurableSpace F := borel _
local instance largeTwistLFieldBorel : BorelSpace F := ⟨rfl⟩
local instance largeTwistLGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance largeTwistLGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance largeTwistLUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F) := borel _
local instance largeTwistLUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance largeTwistLQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F) := borel _
local instance largeTwistLQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

/-- Additive-character scaling transports the complete supplied-measure
pair certificate, including the compatible-quotient existence witness. -/
theorem isPadicPairLPolynomial_characterChange
    (ψ : UnitaryAdditiveCharacter F) (a : Fˣ)
    (μ : AdditiveHaarMeasure F) {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (τ : Representation ℂ (GeneralLinear (n + 1) F) V')
    (P : Polynomial ℂ) :
    IsPadicPairLPolynomial F ψ μ π τ P ↔
      IsPadicPairLPolynomial F (ψ.scale a) μ π τ P := by
  have : SecondCountableTopology F :=
    (⟨⟩ : LocalFieldData F).secondCountableTopology
  refine and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun ν => ?_)
  refine imp_congr_right fun hν => ?_
  have heq := unipotentQuotientHaar_unique F n ν hν
  subst ν
  exact isPairLPolynomial_characterChange_canonical (⟨⟩ : LocalFieldData F)
    n r ψ a μ π τ P

/-- Both rank orders retain the same full certificate under character scaling. -/
theorem isPadicSymmetricLPolynomial_characterChange
    (ψ : UnitaryAdditiveCharacter F) (a : Fˣ)
    (μ : AdditiveHaarMeasure F) {r n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (τ : Representation ℂ (GeneralLinear (n + 1) F) V')
    (P : Polynomial ℂ) :
    IsPadicSymmetricLPolynomial F ψ μ π τ P ↔
      IsPadicSymmetricLPolynomial F (ψ.scale a) μ π τ P := by
  unfold IsPadicSymmetricLPolynomial
  split_ifs
  · exact isPadicPairLPolynomial_characterChange F ψ a μ π τ P
  · exact isPadicPairLPolynomial_characterChange F ψ a μ τ π P

/-- Complete symmetric L certificates commute even in the equal-rank branch. -/
theorem isPadicSymmetricLPolynomial_comm
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (τ : Representation ℂ (GeneralLinear (n + 1) F) V')
    (P : Polynomial ℂ) :
    IsPadicSymmetricLPolynomial F ψ μ π τ P ↔
      IsPadicSymmetricLPolynomial F ψ μ τ π P := by
  by_cases hnr : n < r
  · rw [isPadicSymmetricLPolynomial_of_le hnr.le,
      isPadicSymmetricLPolynomial_of_lt hnr]
  · by_cases hrn : r < n
    · rw [isPadicSymmetricLPolynomial_of_lt hrn,
        isPadicSymmetricLPolynomial_of_le hrn.le]
    · have heq : n = r := by omega
      subst n
      rw [isPadicSymmetricLPolynomial_of_le le_rfl,
        isPadicSymmetricLPolynomial_of_le le_rfl]
      exact isPadicPairLPolynomial_swap_equalRank F ψ μ π τ P

private theorem symmetricLPolynomial_ne_zero
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (τ : Representation ℂ (GeneralLinear (n + 1) F) V')
    (P : Polynomial ℂ) (hP : IsPadicSymmetricLPolynomial F ψ μ π τ P) : P ≠ 0 := by
  unfold IsPadicSymmetricLPolynomial at hP
  split_ifs at hP
  · obtain ⟨⟨hinv, ν, hν⟩, hall⟩ := hP
    let := hinv
    exact (hall ν hν).ne_zero
  · obtain ⟨⟨hinv, ν, hν⟩, hall⟩ := hP
    let := hinv
    exact (hall ν hν).ne_zero

/-- Complete pair-polynomial certificates and the required divisibility on
actual normalized lower induction above one real second-twist threshold. -/
def AdjacentRankLargeTwistLDivisibility
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (χ₀ : Quasicharacter F) : Prop :=
  ∃ C : ℝ, ∀ u : ℝ, C < u →
    let χ := Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.realTwistedCharacter F χ₀ u
    let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
    let ρ := (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced B
      (B.blockTensor (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))
    ∃ P P₀ P₁ : Polynomial ℂ,
      IsPadicSymmetricLPolynomial F ψ μ τ ρ P ∧
      IsPadicSymmetricLPolynomial F ψ μ τ σ P₀ ∧
      IsPadicSymmetricLPolynomial F ψ μ τ (rankOneExtensionCharacter.{uF, uV} F χ) P₁ ∧
      ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * (P₀ * P₁) = Q * P

/-- The actual large-second-twist model gives complete L certificates and
exact product divisibility, with every analytic/image/type premise discharged. -/
theorem adjacentRankLargeTwistLDivisibility
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (hτ : IsOfWhittakerType r (standardCharacter ψ r) τ)
    (χ₀ : Quasicharacter F) :
    AdjacentRankLargeTwistLDivisibility F ψ μ σ τ χ₀ := by
  obtain ⟨ℓ, hℓ⟩ := hσ.exists_ne_zero
  have hτs : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ := by
    simpa only [standardCharacter_scale_neg_one] using
      (isOfWhittakerType_standard_iff_inverse ψ τ).mp hτ
  obtain ⟨ℓ', hℓ'⟩ := hτs.exists_ne_zero
  let μsd : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ := ⟨μ, hself⟩
  obtain ⟨P₀, hP₀⟩ := symmetricLPolynomialExists F ψ μsd r r V V' σ τ hσ hτ
  refine ⟨adjacentRankInducedModelBound F ψ μ hself σ hσ ℓ hℓ χ₀, ?_⟩
  intro u hu
  let χ := Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.realTwistedCharacter F χ₀ u
  let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
  let ρ := (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced B
    (B.blockTensor (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))
  have hρ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) ρ :=
    adjacentRankNormalizedOpposite_isOfWhittakerType F ψ σ hσ χ
  obtain ⟨J, hJ, himage⟩ :=
    (adjacentRankModelImage F ψ μ hself r V σ hσ ℓ hℓ χ₀).choose_spec u hu
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists F ψ μsd (r + 1) r _ V' ρ τ hρ hτ
  have hχ : IsOfWhittakerType 0 (standardCharacter ψ 0) (rankOneCharacter (χ : Fˣ →* ℂˣ)) :=
    rankOneCharacter_isOfWhittakerType F ψ χ
  obtain ⟨P₁, hP₁⟩ := symmetricLPolynomialExists F ψ μsd r 0 V' ℂ τ
    (rankOneCharacter (χ : Fˣ →* ℂˣ)) hτ hχ
  have hcancel : Langlands.twist (((χ : Fˣ →* ℂˣ)⁻¹).comp determinant)
      (rankOneCharacter (χ : Fˣ →* ℂˣ)) = rankOneCharacter 1 := by
    have hone : (1 : Fˣ →* ℂˣ) * (χ : Fˣ →* ℂˣ) = χ :=
      MonoidHom.ext fun _ => one_mul _
    simpa only [hone] using
      twist_rankOneCharacter (χ := (1 : Fˣ →* ℂˣ)) (χ : Fˣ →* ℂˣ)
  have hP₁twist : IsPadicSymmetricLPolynomial F ψ μ
      (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) τ)
      (rankOneCharacter 1) P₁ := by
    simpa only [hcancel] using
      (isPadicSymmetricLPolynomial_twist ψ μ τ
        (rankOneCharacter (χ : Fˣ →* ℂˣ)) (χ : Fˣ →* ℂˣ) P₁).mpr hP₁
  have hP₁s := (isPadicSymmetricLPolynomial_characterChange F ψ (-1) μ _ _ P₁).mp hP₁twist
  have hPair : IsPadicPairLPolynomial F ψ μ ρ τ P :=
    (isPadicSymmetricLPolynomial_of_le (Nat.le_succ r)).mp hP
  obtain ⟨⟨hinv, ν, hν⟩, -⟩ := hPair
  let := hinv
  have hbound := adjacentRankImage_productDenominatorBound F ψ μ hself ν hν
    σ hσ ℓ hℓ χ ρ hρ J hJ himage τ hτs ℓ' hℓ' P₀ P₁ hP₀ hP₁s
  have hnonzero : P₀ * P₁ ≠ 0 := mul_ne_zero
    (symmetricLPolynomial_ne_zero F ψ μ σ τ P₀ hP₀)
    (symmetricLPolynomial_ne_zero F ψ μ τ (rankOneCharacter (χ : Fˣ →* ℂˣ)) P₁ hP₁)
  obtain ⟨Q, e, hdiv⟩ := adjacentRankModelBound_polynomialDivisibility F ψ μ ν hν
    ρ hρ J hJ τ hτs ℓ' hℓ' P (P₀ * P₁) hnonzero hP hbound
  let eχ : (rankOneCharacter (χ : Fˣ →* ℂˣ)).Equiv
      (rankOneExtensionCharacter.{uF, uV} F χ) :=
    Representation.Equiv.mk ULift.moduleEquiv.symm (by intro g; rfl)
  exact ⟨P, P₀, P₁,
    (isPadicSymmetricLPolynomial_comm F ψ μ ρ τ P).mp hP,
    (isPadicSymmetricLPolynomial_comm F ψ μ σ τ P₀).mp hP₀,
    (Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl τ) eχ).mp hP₁,
    Q, e, hdiv⟩

end Langlands.AllField.RankinSelberg.Padic
