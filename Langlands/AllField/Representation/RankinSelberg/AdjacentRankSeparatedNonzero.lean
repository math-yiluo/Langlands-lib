import Langlands.Representation.RankinSelberg.AdjacentRankSeparatedNonzero
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankImageLDivisibility
/-! Nonzero separated continuations in the actual adjacent model image. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankCoefficientConvolution AdjacentRankCorankDenominatorBound AdjacentRankInvariantApproximationData AdjacentRankModelConverges AdjacentRankModelCorankDenominatorBound AdjacentRankNonzeroSeparatedContinuation AdjacentRankProductContinuationData AdjacentRankShellConvolutionAt AdjacentRankShellLowerBounds adjacentAdmissibilityLocalField adjacentAdmissibilityTopology adjacentAdmissibilityValuativeRel adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCoefficientConvolution_of_shell adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualInnerSliceIntegral adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankFiniteProductValue adjacentRankImage_exists_nonzeroSeparatedContinuation adjacentRankImage_productDenominatorBound adjacentRankInducedModelBound adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankInvariantApproximation adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankLowerCompactRepresentation adjacentRankLowerInducingCoordinates adjacentRankLowerTensorCoordinates_action adjacentRankLowerTensorRepresentation adjacentRankLowerTensorRepresentation_isAdmissible adjacentRankMatrixSliceCoefficient adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound adjacentRankMatrixSliceExpansion adjacentRankModelBound_polynomialDivisibility adjacentRankModelConverges_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegral_mul adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModelMap adjacentRankModelMapBorel adjacentRankModelMapDisconnected adjacentRankModelMapGLMeasurable adjacentRankModelMapLocalField adjacentRankModelMapMeasurable adjacentRankModelMapT2 adjacentRankModelMapTopology adjacentRankModelMapValuative adjacentRankModelMap_apply adjacentRankModelStarScalar adjacentRankModelStar_corankOneSlice_eq_before adjacentRankModelStar_separated_rankInclusion adjacentRankModelStar_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankModel_matchedCoefficientConvolution adjacentRankModel_matchedProductContinuation adjacentRankModel_matchedProductContinuation_exists adjacentRankNormalizedInduced_isAdmissible adjacentRankNormalizedOpposite_isOfWhittakerType adjacentRankNormalizedSection adjacentRankNormalizedSectionTensor adjacentRankNormalizedSectionTensor_surjective adjacentRankNormalizedSectionTensor_tmul adjacentRankNormalizedSection_eval adjacentRankNormalizedSection_right adjacentRankProductContinuation_denominatorBound adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_finiteConvolution_of_innerSeparation adjacentRankShell_matchedFiniteConvolution adjacentRankShell_shear_fubini adjacentRankTest_exists_sum_separated adjacentSectionFieldTopology adjacentSectionGLBorel adjacentSectionGLMeasurable adjacentSectionLocalField adjacentSectionT2 adjacentSectionValuativeRel compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuationFieldMeasurableSpace continuationFieldTopology continuationFieldValuation continuationGroupBorelSpace continuationGroupMeasurableSpace continuationLocalField continuationQuotientMeasurableSpace continuationUnipotentBorelSpace continuationUnipotentMeasurableSpace continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel corankOneCoefficient_convergesOnRight corankOneCoefficient_productContinuation corankOneCoefficient_scalarProductContinuation corankOneIntegral_eq_finiteProducts_of_coefficients corankOneIntegral_eq_zeroZero corankOneIntegrand_eq_mul_spectralPoint_zpow corankOneSliceExpansion dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel dualModelFieldBorel dualModelFieldMeasurable dualModelFieldT2 dualModelFieldTopology dualModelFieldTotallyDisconnected dualModelGroupBorel dualModelGroupMeasurable dualModelLocalField dualModelValuativeRel dualRestrictionFieldBorel dualRestrictionFieldMeasurable dualRestrictionFieldT2 dualRestrictionFieldTopology dualRestrictionFieldTotallyDisconnected dualRestrictionGroupBorel dualRestrictionGroupMeasurable dualRestrictionLocalField dualRestrictionValuativeRel equalRankSliceCoefficient_eq_zero_of_pointwise_bound exists_adjacentRankInner_subgroup exists_adjacentRankModelMatrixValues exists_adjacentRankTestWeightLevel exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice hasSum_setIntegral_generalLinearDeterminantSlice imageBoundFieldBorel imageBoundFieldMeasurable imageBoundFieldT2 imageBoundFieldTotallyDisconnected imageBoundGroupBorel imageBoundGroupMeasurable imageBoundLocalField imageBoundQuotientMeasurable imageBoundTopology imageBoundUnipotentBorel imageBoundUnipotentMeasurable imageBoundValuativeRel inducedModelFieldBorel inducedModelFieldMeasurable inducedModelFieldT2 inducedModelFieldTotallyDisconnected inducedModelLocalField inducedModelTopology inducedModelValuativeRel innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices invariantApproximationGLLocallyCompact invariantApproximationGLNonarch invariantApproximationLocalField invariantApproximationNonarchRing invariantApproximationSecondCountable invariantApproximationT2 invariantApproximationTopology invariantApproximationValuativeRel inverseCoefficientAsScaledStandard isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel matchedCoefficientFieldBorel matchedCoefficientFieldMeasurable matchedCoefficientFieldT2 matchedCoefficientFieldTopology matchedCoefficientFieldTotallyDisconnected matchedCoefficientGroupBorel matchedCoefficientGroupMeasurable matchedCoefficientGroupSigmaCompact matchedCoefficientLocalField matchedCoefficientQuotientBorel matchedCoefficientQuotientMeasurable matchedCoefficientUnipotentBorel matchedCoefficientUnipotentMeasurable matchedCoefficientValuativeRel matchedContinuationFieldBorel matchedContinuationFieldMeasurable matchedContinuationFieldT2 matchedContinuationFieldTopology matchedContinuationFieldTotallyDisconnected matchedContinuationGroupBorel matchedContinuationGroupMeasurable matchedContinuationLocalField matchedContinuationQuotientMeasurable matchedContinuationUnipotentBorel matchedContinuationUnipotentMeasurable matchedContinuationValuativeRel matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel matchedShellFieldT2 matchedShellFieldTopology matchedShellGroupBorel matchedShellGroupMeasurable matchedShellGroupSecondCountable matchedShellGroupSigmaCompact matchedShellLocalField matchedShellQuotientLocallyCompact matchedShellQuotientMeasurable matchedShellQuotientSecondCountable matchedShellUnipotentBorel matchedShellUnipotentMeasurable matchedShellValuativeRel matrixWitnessFieldBorel matrixWitnessFieldMeasurable matrixWitnessFieldT2 matrixWitnessFieldTotallyDisconnected matrixWitnessGroupBorel matrixWitnessGroupMeasurable matrixWitnessLocalField matrixWitnessQuotientMeasurable matrixWitnessTopology matrixWitnessUnipotentBorel matrixWitnessUnipotentMeasurable matrixWitnessValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel nonempty_adjacentRankInvariantApproximation oppositeParabolicQuotientCompact productBoundFieldMeasurable productBoundGroupBorel productBoundGroupMeasurable productBoundLocalField productBoundModelAddCommGroup productBoundQuotientMeasurable productBoundTopology productBoundUnipotentBorel productBoundUnipotentMeasurable productBoundValuativeRel productsFieldTopology productsQuotientMeasurableSpace quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel scaledStandardCoefficientAsInverse sectionSurjectivityGLBorel sectionSurjectivityGLMeasurable sectionSurjectivityLocalField sectionSurjectivityT2 sectionSurjectivityTopology sectionSurjectivityValuativeRel separatedNonzeroFieldBorel separatedNonzeroFieldMeasurable separatedNonzeroFieldT2 separatedNonzeroFieldTotallyDisconnected separatedNonzeroGroupBorel separatedNonzeroGroupMeasurable separatedNonzeroLocalField separatedNonzeroQuotientMeasurable separatedNonzeroTopology separatedNonzeroUnipotentBorel separatedNonzeroUnipotentMeasurable separatedNonzeroValuativeRel setIntegral_matrixIntegrand_determinantSlice shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel spectralFieldTopology spectralFieldValuation spectralGroupBorelSpace spectralGroupMeasurableSpace spectralLocalField spectralQuotientBorelSpace spectralQuotientMeasurableSpace
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelConverges AdjacentRankModelImageStatement AdjacentRankModelStarStatement CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockJacquetConvergenceStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelImage adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankStarEquiv adjacentRankStarEquiv_tmul_evaluation adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice symmetricLPolynomialExists twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockGammaRankOne_of_trivial_test twoBlockJacquetConvergence twoBlockLRankOne_of_trivial_test twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
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

local instance separatedNonzeroFieldT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance separatedNonzeroFieldTotallyDisconnected :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance separatedNonzeroFieldMeasurable : MeasurableSpace F := borel _
local instance separatedNonzeroFieldBorel : BorelSpace F := ⟨rfl⟩
local instance separatedNonzeroGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance separatedNonzeroGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance separatedNonzeroUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F) := borel _
local instance separatedNonzeroUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance separatedNonzeroQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F) := borel _
local instance separatedNonzeroQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

/-- A genuinely nonzero actual continuation on a separated ambient coefficient. -/
def AdjacentRankNonzeroSeparatedContinuation
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (ν : Measure (LeftUnipotentQuotient r F))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F) VU)
    (J : glFunctionals ψ (r + 1) π)
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) : Prop :=
  ∃ (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
    (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
    (R : RationalFunctions),
    (∀ g, U.val.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g) ∧
    HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U.val
      (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) s) R ∧ R ≠ 0

/-- Whole-function image equality and a nonzero corank continuation force
one separated coefficient to have a nonzero continuation. -/
theorem adjacentRankImage_exists_nonzeroSeparatedContinuation
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ)
    (χ : Quasicharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F) VU)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (J : glFunctionals ψ (r + 1) π) (hJ : J.val ≠ 0)
    (himage : Set.range (adjacentRankModelMap F ψ μ hself σ ℓ χ hσ.1.1) =
      Set.range (fun v : π.asModule => fun g => J.val (π g v)))
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (hnonzero : ∃ (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
      (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
      (R : RationalFunctions),
      HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) s) R ∧ R ≠ 0) :
    AdjacentRankNonzeroSeparatedContinuation F ψ μ hself ν σ ℓ χ π J τ ℓ' := by
  classical
  have : SigmaCompactSpace (GeneralLinear (r + 1) F) :=
    (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (r + 1)
  have : SigmaCompactSpace (LeftUnipotentQuotient r F) := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr (Quotient.mk_surjective (s := QuotientGroup.rightRel
      (upperUnipotent (r + 1) F)))]
    exact isSigmaCompact_range continuous_quot_mk
  have : ν.Regular := hν.regular
  have : SigmaFinite ν := inferInstance
  have : SFinite (rectangularMeasure μ 0 (r + 1)) := by
    rw [rectangularMeasure_zero_rows]
    infer_instance
  obtain ⟨U, W', R, hR, hR0⟩ := hnonzero
  let I := adjacentRankModelMap F ψ μ hself σ ℓ χ hσ.1.1
  have hreal (Ψ : adjacentRankTestSpace ψ σ ℓ) :
      ∃ U : (glCoefficientModel ψ (r + 1) π J).toSubmodule,
        ∀ g, U.val.val g = I Ψ g := by
    obtain ⟨v, hv⟩ := himage.le ⟨Ψ, rfl⟩
    exact ⟨modelMap π J v, fun g => congrFun hv g⟩
  choose L hL using hreal
  let Lmap : adjacentRankTestSpace ψ σ ℓ →ₗ[ℂ]
      (glCoefficientModel ψ (r + 1) π J).toSubmodule :=
    { toFun := L
      map_add' := by
        intro Ψ Θ
        apply Subtype.ext
        apply Subtype.ext
        funext g
        change (L (Ψ + Θ)).val.val g = (L Ψ).val.val g + (L Θ).val.val g
        rw [hL, hL, hL]
        exact congrFun (I.map_add Ψ Θ) g
      map_smul' := by
        intro c Ψ
        apply Subtype.ext
        apply Subtype.ext
        funext g
        change (L (c • Ψ)).val.val g = c * (L Ψ).val.val g
        rw [hL, hL]
        exact congrFun (I.map_smul c Ψ) g }
  let ℓinv := functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ'
  have hτinv : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ := by
    simpa only [standardCharacter_scale_neg_one] using hτ
  let hA : UnequalRankAnalyticAt 0 0 rfl qF ψ abv ν
      (rectangularMeasure μ 0 (r + 1)) π τ J ℓinv :=
    unequalRankAnalytic F (⟨⟩ : LocalFieldData F) r 0 0 ψ ν hν μ
      VU V' π τ hπ hτinv J ℓinv hJ hℓ'
  let C := blockContinuationFamily (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hA
  have hC (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
      (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule) :
      HasRationalContinuation qF
        (fun s => corankOneIntegral ψ abv ν U.val
          (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) s)
        (C U (scaledStandardCoefficientAsInverse F ψ τ ℓ' W')) := by
    exact RationalContinuationLinear.continuation_of_eq_on_right
      (blockContinuationFamily_spec (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
        hA U (scaledStandardCoefficientAsInverse F ψ τ ℓ' W'))
      ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) s⟩
  let CL := (C.flip (scaledStandardCoefficientAsInverse F ψ τ ℓ' W')).comp Lmap
  have hmem : U.val.val ∈ Set.range I := by
    have hUm := U.property
    unfold glCoefficientModel coefficientModel at hUm
    obtain ⟨v, hv⟩ := hUm
    apply himage.symm.le
    exact ⟨v, congrArg Subtype.val hv⟩
  obtain ⟨Ψ, hΨ⟩ := hmem
  have hLU : Lmap Ψ = U := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact (hL Ψ g).trans (congrFun hΨ g)
  have hvalue : R = CL Ψ := by
    have heq := hR.unique (⟨⟩ : LocalFieldData F).residueCardinality_gt_one (hC U W')
    simpa only [CL, LinearMap.comp_apply, LinearMap.flip_apply, hLU] using heq
  have hex : ∃ (Φ : GodementJacquet.MatrixTestFunction r F)
      (φ : SchwartzBruhat (Fin (r + 1) → F))
      (W : (glCoefficientModel ψ r σ ℓ).toSubmodule),
      CL (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) ≠ 0 := by
    by_contra! hzero
    have htests (Θ : adjacentRankTestSpace ψ σ ℓ) : CL Θ = 0 := by
      induction Θ using adjacentRankTestSpace_induction ψ σ ℓ with
      | tmul Φ W =>
        obtain ⟨N, A, b, hΦ⟩ := adjacentRankTest_exists_sum_separated F Φ
        rw [hΦ, TensorProduct.sum_tmul, map_sum]
        exact Finset.sum_eq_zero fun i _ => hzero (A i) (b i) W
      | add Θ Λ hΘ hΛ => rw [map_add, hΘ, hΛ, add_zero]
    exact hR0 (hvalue.trans (htests Ψ))
  obtain ⟨Φ, φ, W, hnonzero⟩ := hex
  exact ⟨Φ, φ, W, Lmap (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W), W',
    CL (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W), hL _, hC _ W', hnonzero⟩

end Langlands.AllField.RankinSelberg.Padic
