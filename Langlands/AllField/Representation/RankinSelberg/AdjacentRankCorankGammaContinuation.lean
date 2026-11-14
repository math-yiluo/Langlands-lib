import Langlands.Representation.RankinSelberg.AdjacentRankCorankGammaContinuation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankCertifiedRealRay
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankClearedContinuation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankDualEntireCoefficientFamily
import Langlands.AllField.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationProof
/-! Actual corank integrals in second-block gamma continuation. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankCoefficientConvolution AdjacentRankCorankDenominatorBound AdjacentRankInvariantApproximationData AdjacentRankLargeTwistLDivisibility AdjacentRankModelConverges AdjacentRankModelCorankDenominatorBound AdjacentRankProductContinuationData AdjacentRankShellConvolutionAt AdjacentRankShellLowerBounds HasCommonCompactOpenRightLevel SecondBlockCorankRealRayCertificates SecondBlockCorankRealRayClearing SecondBlockCorankRealRayDenominatorBound SecondBlockCorankRealRayGammaCertificates adjacentAdmissibilityLocalField adjacentAdmissibilityTopology adjacentAdmissibilityValuativeRel adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCoefficientConvolution_of_shell adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualCoefficientFamily adjacentRankDualCoefficientFamily_integrable_entire adjacentRankDualInnerSliceIntegral adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankDualWhittakerFamily adjacentRankDualWhittakerFamily_level_entire adjacentRankFiniteProductValue adjacentRankImage_productDenominatorBound adjacentRankInducedModelBound adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankInvariantApproximation adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankLargeTwistLDivisibility adjacentRankLowerCompactRepresentation adjacentRankLowerInducingCoordinates adjacentRankLowerTensorCoordinates_action adjacentRankLowerTensorRepresentation adjacentRankLowerTensorRepresentation_isAdmissible adjacentRankMatrixSliceCoefficient adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound adjacentRankMatrixSliceExpansion adjacentRankModelBound_polynomialDivisibility adjacentRankModelConverges_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegral_mul adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModelMap adjacentRankModelMapBorel adjacentRankModelMapDisconnected adjacentRankModelMapGLMeasurable adjacentRankModelMapLocalField adjacentRankModelMapMeasurable adjacentRankModelMapT2 adjacentRankModelMapTopology adjacentRankModelMapValuative adjacentRankModelMap_apply adjacentRankModelStarScalar adjacentRankModelStar_corankOneSlice_eq_before adjacentRankModelStar_separated_rankInclusion adjacentRankModelStar_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankModel_matchedCoefficientConvolution adjacentRankModel_matchedProductContinuation adjacentRankModel_matchedProductContinuation_exists adjacentRankNormalizedInduced_isAdmissible adjacentRankNormalizedOpposite_isOfWhittakerType adjacentRankNormalizedSection adjacentRankNormalizedSectionTensor adjacentRankNormalizedSectionTensor_surjective adjacentRankNormalizedSectionTensor_tmul adjacentRankNormalizedSection_eval adjacentRankNormalizedSection_right adjacentRankProductContinuation_denominatorBound adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_finiteConvolution_of_innerSeparation adjacentRankShell_matchedFiniteConvolution adjacentRankShell_shear_fubini adjacentRankTest_exists_sum_separated adjacentSectionFieldTopology adjacentSectionGLBorel adjacentSectionGLMeasurable adjacentSectionLocalField adjacentSectionT2 adjacentSectionValuativeRel certifiedRealRayFieldMeasurable certifiedRealRayGroupBorel certifiedRealRayGroupMeasurable certifiedRealRayLocalField certifiedRealRayQuotientMeasurable certifiedRealRayTopology certifiedRealRayUnipotentBorel certifiedRealRayUnipotentMeasurable certifiedRealRayValuation clearedContinuationFieldMeasurable clearedContinuationGroupBorel clearedContinuationGroupMeasurable clearedContinuationLocalField clearedContinuationQuotientMeasurable clearedContinuationTopology clearedContinuationUnipotentBorel clearedContinuationUnipotentMeasurable clearedContinuationValuation clearingKernelTopology compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuationFieldMeasurableSpace continuationFieldTopology continuationFieldValuation continuationGroupBorelSpace continuationGroupMeasurableSpace continuationLocalField continuationQuotientMeasurableSpace continuationUnipotentBorelSpace continuationUnipotentMeasurableSpace continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel corankClearing_denominatorBound corankCoefficientFamily corankCoefficientFamily_integrable_entire corankCoefficientSeries corankGammaFieldMeasurable corankGammaGroupBorel corankGammaGroupMeasurable corankGammaLocalField corankGammaQuotientMeasurable corankGammaTopology corankGammaUnipotentBorel corankGammaUnipotentMeasurable corankGammaValuation corankOneCoefficient_clearing_denominatorBound corankOneCoefficient_continuationData corankOneCoefficient_convergesOnRight corankOneCoefficient_denominatorBound_clearing corankOneCoefficient_denominatorBound_of_certificate corankOneCoefficient_productContinuation corankOneCoefficient_scalarProductContinuation corankOneIntegral_eq_finiteProducts_of_coefficients corankOneIntegral_eq_zeroZero corankOneIntegrand_eq_mul_spectralPoint_zpow corankOneSliceExpansion dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel dualEntireGroupBorel dualEntireGroupMeasurable dualEntireLocalField dualEntireQuotientMeasurable dualEntireTopology dualEntireUnipotentBorel dualEntireUnipotentMeasurable dualEntireValuation dualModelFieldBorel dualModelFieldMeasurable dualModelFieldT2 dualModelFieldTopology dualModelFieldTotallyDisconnected dualModelGroupBorel dualModelGroupMeasurable dualModelLocalField dualModelValuativeRel dualRestrictionFieldBorel dualRestrictionFieldMeasurable dualRestrictionFieldT2 dualRestrictionFieldTopology dualRestrictionFieldTotallyDisconnected dualRestrictionGroupBorel dualRestrictionGroupMeasurable dualRestrictionLocalField dualRestrictionValuativeRel entireCoefficientGroupBorel entireCoefficientGroupMeasurable entireCoefficientLocalField entireCoefficientQuotientMeasurable entireCoefficientTopology entireCoefficientUnipotentBorel entireCoefficientUnipotentMeasurable entireCoefficientValuation equalRankSliceCoefficient_eq_zero_of_pointwise_bound exists_adjacentRankInner_subgroup exists_adjacentRankModelMatrixValues exists_adjacentRankTestWeightLevel exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice hasSum_setIntegral_generalLinearDeterminantSlice imageBoundFieldBorel imageBoundFieldMeasurable imageBoundFieldT2 imageBoundFieldTotallyDisconnected imageBoundGroupBorel imageBoundGroupMeasurable imageBoundLocalField imageBoundQuotientMeasurable imageBoundTopology imageBoundUnipotentBorel imageBoundUnipotentMeasurable imageBoundValuativeRel inducedModelFieldBorel inducedModelFieldMeasurable inducedModelFieldT2 inducedModelFieldTotallyDisconnected inducedModelLocalField inducedModelTopology inducedModelValuativeRel innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices invariantApproximationGLLocallyCompact invariantApproximationGLNonarch invariantApproximationLocalField invariantApproximationNonarchRing invariantApproximationSecondCountable invariantApproximationT2 invariantApproximationTopology invariantApproximationValuativeRel inverseCoefficientAsScaledStandard isClopen_adjacentRankJointShell isPadicPairLPolynomial_characterChange isPadicSymmetricLPolynomial_characterChange isPadicSymmetricLPolynomial_comm jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel largeTwistLFieldBorel largeTwistLFieldMeasurable largeTwistLFieldT2 largeTwistLFieldTotallyDisconnected largeTwistLGroupBorel largeTwistLGroupMeasurable largeTwistLLocalField largeTwistLQuotientBorel largeTwistLQuotientMeasurable largeTwistLTopology largeTwistLUnipotentBorel largeTwistLUnipotentMeasurable largeTwistLValuativeRel matchedCoefficientFieldBorel matchedCoefficientFieldMeasurable matchedCoefficientFieldT2 matchedCoefficientFieldTopology matchedCoefficientFieldTotallyDisconnected matchedCoefficientGroupBorel matchedCoefficientGroupMeasurable matchedCoefficientGroupSigmaCompact matchedCoefficientLocalField matchedCoefficientQuotientBorel matchedCoefficientQuotientMeasurable matchedCoefficientUnipotentBorel matchedCoefficientUnipotentMeasurable matchedCoefficientValuativeRel matchedContinuationFieldBorel matchedContinuationFieldMeasurable matchedContinuationFieldT2 matchedContinuationFieldTopology matchedContinuationFieldTotallyDisconnected matchedContinuationGroupBorel matchedContinuationGroupMeasurable matchedContinuationLocalField matchedContinuationQuotientMeasurable matchedContinuationUnipotentBorel matchedContinuationUnipotentMeasurable matchedContinuationValuativeRel matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel matchedShellFieldT2 matchedShellFieldTopology matchedShellGroupBorel matchedShellGroupMeasurable matchedShellGroupSecondCountable matchedShellGroupSigmaCompact matchedShellLocalField matchedShellQuotientLocallyCompact matchedShellQuotientMeasurable matchedShellQuotientSecondCountable matchedShellUnipotentBorel matchedShellUnipotentMeasurable matchedShellValuativeRel matrixWitnessFieldBorel matrixWitnessFieldMeasurable matrixWitnessFieldT2 matrixWitnessFieldTotallyDisconnected matrixWitnessGroupBorel matrixWitnessGroupMeasurable matrixWitnessLocalField matrixWitnessQuotientMeasurable matrixWitnessTopology matrixWitnessUnipotentBorel matrixWitnessUnipotentMeasurable matrixWitnessValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel nonempty_adjacentRankInvariantApproximation oppositeParabolicQuotientCompact productBoundFieldMeasurable productBoundGroupBorel productBoundGroupMeasurable productBoundLocalField productBoundModelAddCommGroup productBoundQuotientMeasurable productBoundTopology productBoundUnipotentBorel productBoundUnipotentMeasurable productBoundValuativeRel productsFieldTopology productsQuotientMeasurableSpace quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel realRayClearingFieldMeasurable realRayClearingGroupBorel realRayClearingGroupMeasurable realRayClearingLocalField realRayClearingQuotientMeasurable realRayClearingTopology realRayClearingUnipotentBorel realRayClearingUnipotentMeasurable realRayClearingValuation scaledStandardCoefficientAsInverse secondBlockDeformed_isOfWhittakerType secondBlock_corankClearing_at_zero secondBlock_corankGamma_at_zero secondBlock_entireCorankFamily secondBlock_realRayClearing_of_certificates secondBlock_realRayClearing_of_denominatorBound secondBlock_realRayDenominatorBound_of_certificates secondBlock_whittakerFamily secondCorankGroupBorel secondCorankGroupMeasurable secondCorankLocalField secondCorankQuotientMeasurable secondCorankTopology secondCorankUnipotentBorel secondCorankUnipotentMeasurable secondCorankValuation sectionSurjectivityGLBorel sectionSurjectivityGLMeasurable sectionSurjectivityLocalField sectionSurjectivityT2 sectionSurjectivityTopology sectionSurjectivityValuativeRel setIntegral_matrixIntegrand_determinantSlice shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel spectralFieldTopology spectralFieldValuation spectralGroupBorelSpace spectralGroupMeasurableSpace spectralLocalField spectralQuotientBorelSpace spectralQuotientMeasurableSpace symmetricLPolynomial_determinantComplexPower
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelConverges AdjacentRankModelImageStatement AdjacentRankModelStarStatement CharacterChangeCompatibleMeasureStatement CharacterChangeRectangularHaarStatement CharacterChangeRectangularProductStatement CorankOneEntireSliceStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockJacquetConvergenceStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockSecondWhittakerDeformationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement UnramifiedTwistLFactorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelImage adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankStarEquiv adjacentRankStarEquiv_tmul_evaluation adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus characterChangeRectangularHaarStatement characterChangeRectangularProductStatement continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units corankOneEntireSlice determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_canonical isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicPairLPolynomial_unramified_of_transport isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist isPadicSymmetricLPolynomial_unramified_of_transport isPairLPolynomial_characterChange_canonical isUnequalRankLPolynomial_characterChange_canonical iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice symmetricLPolynomialExists twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockGammaRankOne_of_trivial_test twoBlockJacquetConvergence twoBlockLRankOne_of_trivial_test twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockSecondDeformedBlocks twoBlockSecondDeformedBlocks_zero twoBlockSecondDeformedInduced twoBlockSecondWhittakerDeformation twoBlockWhittakerDeformation unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentQuotientHaar_characterChange unipotentQuotientHaar_sigmaFinite_normalized unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel unramifiedTwistLFactor unramifiedTwistLFactor_of_transport whittakerRationalValues_eq_rankOneModelValues whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_canonical zetaSpan_equalRank_characterChange_normalized zetaSpan_unequalRank_characterChange_canonical
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement adjacentRankUnipotentFourier padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic exists_compactOpen_glCoefficientRightStabilizer functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.ParameterSpecialization
open Langlands.RankinSelberg.AdjacentGammaContinuation
open scoped BigOperators

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance corankGammaFieldMeasurable : MeasurableSpace F := borel _
local instance corankGammaFieldBorel : BorelSpace F := ⟨rfl⟩
local instance corankGammaGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F) := borel _
local instance corankGammaGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance corankGammaUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F) := borel _
local instance corankGammaUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance corankGammaQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F) := borel _
local instance corankGammaQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F) := ⟨rfl⟩

local notation "T" => (⟨⟩ : LocalFieldData F)
local notation "abv" => normalizedAbsoluteValue T
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

/-- Full type gives a rational continuation and an actual absolute spectral
expansion of the same corank coefficient vector. -/
theorem corankOneCoefficient_continuationData
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    (μ : AdditiveHaarMeasure F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1 + 1) F) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) W)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓU : glFunctionals ψ (r + 1) π) (hℓU : ℓU.val ≠ 0)
    (ℓprime : glInverseFunctionals ψ r τ) (hℓprime : ℓprime.val ≠ 0)
    (U : (coefficientModel π ℓU).toSubmodule)
    (Wprime : (coefficientModel τ ℓprime).toSubmodule) :
    ∃ R : RationalFunctions,
      HasRationalContinuation qF (fun s =>
        corankOneIntegral ψ abv ν U.val Wprime.val s) R ∧
      HasAbsoluteBilateralSpectralExpansion qF
        (corankCoefficientSeries F ψ ν U.val Wprime.val)
        (fun s => corankOneIntegral ψ abv ν U.val Wprime.val s) := by
  have han := unequalRankAnalytic F T r 0 0 ψ ν hν μ
    V W π τ hπ hτ ℓU ℓprime hℓU hℓprime
  obtain ⟨R, hR⟩ := han.2.1 U Wprime
  have hRc := RationalContinuationLinear.continuation_of_eq_on_right hR
    ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ U.val Wprime.val s⟩
  obtain ⟨C, hC⟩ := corankOneCoefficient_convergesOnRight F ψ ν hν μ
    π τ hπ hτ ℓU ℓprime hℓU hℓprime U Wprime
  exact ⟨R, hRc, C, fun s hs =>
    corankOneSliceExpansion F ψ U.val Wprime.val ν s (hC s hs)⟩

/-- Complete real-ray certificates for the actual second-block deformation
with the fixed spectral product. -/
def SecondBlockCorankRealRayGammaCertificates
    {r : ℕ} (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F)
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (G₀ G₁ : RationalFunctions) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u →
    IsPadicSymmetricGammaFactor F ψ μ
      (twoBlockSecondDeformedInduced F m h σ (u : ℂ)) τ
      (spectralGammaProduct qF (⟨⟩ : LocalFieldData F).residueCardinality_gt_one G₀ G₁ (u : ℂ))

/-- Continue the real-ray gamma products to every specified original model
vector, using its actual original and translated dual corank integrals. -/
theorem secondBlock_corankGamma_at_zero
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = (r + 1) + 1)
    {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (ℓ₀ : glFunctionals ψ (r + 1) (twoBlockSecondDeformedInduced F m h σ 0))
    (hℓ₀ : ℓ₀.val ≠ 0)
    (W₀ : (coefficientModel (twoBlockSecondDeformedInduced F m h σ 0) ℓ₀).toSubmodule)
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    (μ : AdditiveHaarMeasure F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓprime : glInverseFunctionals ψ r τ) (hℓprime : ℓprime.val ≠ 0)
    (Wprime : (coefficientModel τ ℓprime).toSubmodule)
    (ζ : ℂˣ) (hζ : HasModelMinusOneScalar τ ℓprime ζ)
    (G₀ G₁ : RationalFunctions)
    (P₀ P₁ : Polynomial ℂ) (hP : P₀ * P₁ ≠ 0) (C : ℝ)
    (hclear : SecondBlockCorankRealRayClearing F ψ m h σ ν Wprime.val P₀ P₁ C)
    (hgamma : SecondBlockCorankRealRayGammaCertificates F ψ μ m h σ τ G₀ G₁ C) :
    ∃ R Rd : RationalFunctions,
      HasRationalContinuation qF (fun s =>
        corankOneIntegral ψ abv ν W₀.val Wprime.val s) R ∧
      HasRationalContinuation qF
        (dualUnequalRankModelIntegralAt (Nat.lt_succ_self r) 0 0 rfl ψ abv ν μ
          (twoBlockSecondDeformedInduced F m h σ 0) τ ℓ₀ ℓprime W₀ Wprime) Rd ∧
      GammaFunctionalEquation qF ζ (r + 1) (G₀ * G₁) R Rd := by
  classical
  obtain ⟨U, hzero, hcoeff, hK, hU, -, hae⟩ :=
    secondBlock_entireCorankFamily F twoBlockSecondWhittakerDeformation ψ r
      m h σ hσ ℓ₀ hℓ₀ W₀ ν hν τ hτ ℓprime Wprime
  have hade := (adjacentRankDualCoefficientFamily_integrable_entire F ψ r ν hν
    τ hτ ℓprime Wprime U hK hU).2
  let I := fun u s => corankOneIntegral ψ abv ν (U u) Wprime.val s
  let Id := fun u s => corankOneIntegral (ψ.scale (-1)) abv ν
    (adjacentRankDualWhittakerFamily F ψ r U u) (secondDualFunction ψ r Wprime.val) s
  have hdata : ∀ u : ℂ, ∃ R Rd : RationalFunctions,
      HasRationalContinuation qF (I u) R ∧
      HasRationalContinuation qF (Id u) Rd ∧
      HasAbsoluteBilateralSpectralExpansion qF
        (corankCoefficientFamily F ψ ν Wprime.val U u) (I u) ∧
      HasAbsoluteBilateralSpectralExpansion qF
        (adjacentRankDualCoefficientFamily F ψ ν Wprime.val U u) (Id u) := by
    intro u
    obtain ⟨ℓu, hℓu, v, hv⟩ := hcoeff u
    let π := twoBlockSecondDeformedInduced F m h σ u
    have hπ := secondBlockDeformed_isOfWhittakerType F ψ m h σ hσ u
    let f := modelMap π ℓu v
    have hf : f.val = U u := hv
    obtain ⟨R, hR, ha⟩ := corankOneCoefficient_continuationData F ψ ν hν μ
      π τ hπ hτ ℓu hℓu ℓprime hℓprime f Wprime
    have hπd : IsOfWhittakerType (r + 1)
        (standardCharacter (ψ.scale (-1)) (r + 1)) (inverseTransposePullback π) := by
      simpa only [standardCharacter_scale_neg_one] using
        isOfWhittakerType_inverseTransposePullback ψ π hπ
    have hτd : IsOfWhittakerType r (inverseStandardCharacter (ψ.scale (-1)) r)
        (inverseTransposePullback τ) := by
      simpa only [inverseStandardCharacter_scale_neg_one] using
        isOfWhittakerType_inverseTransposePullback_inverse ψ τ hτ
    let fd := translatedFirstDualModelEquiv ψ π ℓu
      (blockWeylAt r (r + 1) (Nat.lt_succ_self r)) f
    obtain ⟨Rd, hRd, had⟩ := corankOneCoefficient_continuationData F (ψ.scale (-1))
      ν hν μ (inverseTransposePullback π) (inverseTransposePullback τ) hπd hτd
      (firstDualFunctional ψ π ℓu) (firstDualFunctional_ne_zero ψ π hℓu)
      (secondDualFunctional ψ τ ℓprime) (secondDualFunctional_ne_zero ψ τ hℓprime)
      fd (secondDualModelMap ψ τ ℓprime Wprime)
    rw [hf] at hR ha
    have hfd : fd.val = adjacentRankDualWhittakerFamily F ψ r U u := by
      change translateWhittaker _ _ (firstDualFunction _ _ f.val) _ = _
      rw [hf]
      rfl
    change HasRationalContinuation qF
      (fun s => corankOneIntegral _ abv ν fd.val (secondDualFunction ψ r Wprime.val) s)
      Rd at hRd
    change HasAbsoluteBilateralSpectralExpansion qF
      (corankCoefficientSeries F _ ν fd.val (secondDualFunction ψ r Wprime.val))
      (fun s => corankOneIntegral _ abv ν fd.val (secondDualFunction ψ r Wprime.val) s)
      at had
    rw [hfd] at hRd had
    exact ⟨R, Rd, hR, hRd, ha, had⟩
  choose R Rd hR hRd ha had using hdata
  have hFE : ∀ u : ℝ, C < u →
      GammaFunctionalEquation qF ζ (r + 1)
        (spectralGammaProduct qF (⟨⟩ : LocalFieldData F).residueCardinality_gt_one G₀ G₁ (u : ℂ))
        (R (u : ℂ)) (Rd (u : ℂ)) := by
    intro u hu
    obtain ⟨ℓu, hℓu, v, hv⟩ := hcoeff (u : ℂ)
    let π := twoBlockSecondDeformedInduced F m h σ (u : ℂ)
    let f := modelMap π ℓu v
    have hf : f.val = U (u : ℂ) := hv
    have hg := (isPairGammaFactor_of_lt (Nat.lt_succ_self r)).mp
      ((isPadicSymmetricGammaFactor_of_le (Nat.le_succ r)).mp (hgamma u hu))
    obtain ⟨ζu, hζu, hall⟩ := hg.2.2.2 ν hν ℓu ℓprime hℓu hℓprime
    obtain rfl := hζu.unique hℓprime hζ
    obtain ⟨S, Sd, hS, hSd, hN⟩ := (hall 0 0 rfl).2 f Wprime
    have hSc := RationalContinuationLinear.continuation_of_eq_on_right hS
      ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ f.val Wprime.val s⟩
    have hSdc := RationalContinuationLinear.continuation_of_eq_on_right hSd
      ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F (ψ.scale (-1)) ν μ
        (translateWhittaker _ _ (firstDualFunction ψ (r + 1) f.val)
          (blockWeylAt r (r + 1) (Nat.lt_succ_self r)))
        (secondDualFunction ψ r Wprime.val) s⟩
    rw [hf] at hSc hSdc
    have he : S = R (u : ℂ) := hSc.unique (⟨⟩ : LocalFieldData F).residueCardinality_gt_one (hR _)
    have hed : Sd = Rd (u : ℂ) := hSdc.unique (⟨⟩ : LocalFieldData F).residueCardinality_gt_one (hRd _)
    simpa only [he, hed] using hN
  have hclears : ∀ u : ℝ, C < u → ∃ L : LaurentPolynomial ℂ,
      spectralClearingKernel qF P₀ P₁ (u : ℂ) •
        corankCoefficientFamily F ψ ν Wprime.val U (u : ℂ) =
          BilateralLaurentSeries.ofLaurentPolynomial L := by
    intro u hu
    obtain ⟨ℓu, hℓu, v, hv⟩ := hcoeff (u : ℂ)
    obtain ⟨L, hL⟩ := hclear u hu ℓu hℓu v
    rw [hv] at hL
    exact ⟨L, hL.symm⟩
  have hN := gammaFE_spectralProduct_at_zero (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
    G₀ G₁ P₀ P₁ hP hae hade hR hRd ha had C hclears hFE
  refine ⟨R 0, Rd 0, ?_, ?_, hN⟩
  · simpa only [I, hzero] using hR 0
  · apply RationalContinuationLinear.continuation_of_eq_on_right (hRd 0)
    refine ⟨0, fun s _ => ?_⟩
    change dualUnequalRankModelIntegralAt _ 0 0 rfl ψ abv ν μ
      _ τ ℓ₀ ℓprime W₀ Wprime s = Id 0 s
    unfold dualUnequalRankModelIntegralAt
    rw [← hzero]
    exact (corankOneIntegral_eq_zeroZero F (ψ.scale (-1)) ν μ _ _ s).symm

end Langlands.AllField.RankinSelberg.Padic
