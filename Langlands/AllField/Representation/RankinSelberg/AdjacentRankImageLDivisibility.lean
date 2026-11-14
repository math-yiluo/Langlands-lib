import Langlands.Representation.RankinSelberg.AdjacentRankImageLDivisibility
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankInducedModelContinuation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankProductDenominatorBound
/-! Extend the actual separated product denominator bounds through the whole model image. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankCoefficientConvolution AdjacentRankCorankDenominatorBound AdjacentRankInvariantApproximationData AdjacentRankModelConverges AdjacentRankModelCorankDenominatorBound AdjacentRankProductContinuationData AdjacentRankShellConvolutionAt AdjacentRankShellLowerBounds adjacentAdmissibilityLocalField adjacentAdmissibilityTopology adjacentAdmissibilityValuativeRel adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCoefficientConvolution_of_shell adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualInnerSliceIntegral adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankFiniteProductValue adjacentRankImage_productDenominatorBound adjacentRankInducedModelBound adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankInvariantApproximation adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankLowerCompactRepresentation adjacentRankLowerInducingCoordinates adjacentRankLowerTensorCoordinates_action adjacentRankLowerTensorRepresentation adjacentRankLowerTensorRepresentation_isAdmissible adjacentRankMatrixSliceCoefficient adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound adjacentRankMatrixSliceExpansion adjacentRankModelBound_polynomialDivisibility adjacentRankModelConverges_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegral_mul adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModelMap adjacentRankModelMapBorel adjacentRankModelMapDisconnected adjacentRankModelMapGLMeasurable adjacentRankModelMapLocalField adjacentRankModelMapMeasurable adjacentRankModelMapT2 adjacentRankModelMapTopology adjacentRankModelMapValuative adjacentRankModelMap_apply adjacentRankModelStarScalar adjacentRankModelStar_corankOneSlice_eq_before adjacentRankModelStar_separated_rankInclusion adjacentRankModelStar_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankModel_matchedCoefficientConvolution adjacentRankModel_matchedProductContinuation adjacentRankModel_matchedProductContinuation_exists adjacentRankNormalizedInduced_isAdmissible adjacentRankNormalizedOpposite_isOfWhittakerType adjacentRankNormalizedSection adjacentRankNormalizedSectionTensor adjacentRankNormalizedSectionTensor_surjective adjacentRankNormalizedSectionTensor_tmul adjacentRankNormalizedSection_eval adjacentRankNormalizedSection_right adjacentRankProductContinuation_denominatorBound adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_finiteConvolution_of_innerSeparation adjacentRankShell_matchedFiniteConvolution adjacentRankShell_shear_fubini adjacentRankTest_exists_sum_separated adjacentSectionFieldTopology adjacentSectionGLBorel adjacentSectionGLMeasurable adjacentSectionLocalField adjacentSectionT2 adjacentSectionValuativeRel compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuationFieldMeasurableSpace continuationFieldTopology continuationFieldValuation continuationGroupBorelSpace continuationGroupMeasurableSpace continuationLocalField continuationQuotientMeasurableSpace continuationUnipotentBorelSpace continuationUnipotentMeasurableSpace continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel corankOneCoefficient_convergesOnRight corankOneCoefficient_productContinuation corankOneCoefficient_scalarProductContinuation corankOneIntegral_eq_finiteProducts_of_coefficients corankOneIntegral_eq_zeroZero corankOneIntegrand_eq_mul_spectralPoint_zpow corankOneSliceExpansion dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel dualModelFieldBorel dualModelFieldMeasurable dualModelFieldT2 dualModelFieldTopology dualModelFieldTotallyDisconnected dualModelGroupBorel dualModelGroupMeasurable dualModelLocalField dualModelValuativeRel dualRestrictionFieldBorel dualRestrictionFieldMeasurable dualRestrictionFieldT2 dualRestrictionFieldTopology dualRestrictionFieldTotallyDisconnected dualRestrictionGroupBorel dualRestrictionGroupMeasurable dualRestrictionLocalField dualRestrictionValuativeRel equalRankSliceCoefficient_eq_zero_of_pointwise_bound exists_adjacentRankInner_subgroup exists_adjacentRankModelMatrixValues exists_adjacentRankTestWeightLevel exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice hasSum_setIntegral_generalLinearDeterminantSlice imageBoundFieldBorel imageBoundFieldMeasurable imageBoundFieldT2 imageBoundFieldTotallyDisconnected imageBoundGroupBorel imageBoundGroupMeasurable imageBoundLocalField imageBoundQuotientMeasurable imageBoundTopology imageBoundUnipotentBorel imageBoundUnipotentMeasurable imageBoundValuativeRel inducedModelFieldBorel inducedModelFieldMeasurable inducedModelFieldT2 inducedModelFieldTotallyDisconnected inducedModelLocalField inducedModelTopology inducedModelValuativeRel innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices invariantApproximationGLLocallyCompact invariantApproximationGLNonarch invariantApproximationLocalField invariantApproximationNonarchRing invariantApproximationSecondCountable invariantApproximationT2 invariantApproximationTopology invariantApproximationValuativeRel inverseCoefficientAsScaledStandard isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel matchedCoefficientFieldBorel matchedCoefficientFieldMeasurable matchedCoefficientFieldT2 matchedCoefficientFieldTopology matchedCoefficientFieldTotallyDisconnected matchedCoefficientGroupBorel matchedCoefficientGroupMeasurable matchedCoefficientGroupSigmaCompact matchedCoefficientLocalField matchedCoefficientQuotientBorel matchedCoefficientQuotientMeasurable matchedCoefficientUnipotentBorel matchedCoefficientUnipotentMeasurable matchedCoefficientValuativeRel matchedContinuationFieldBorel matchedContinuationFieldMeasurable matchedContinuationFieldT2 matchedContinuationFieldTopology matchedContinuationFieldTotallyDisconnected matchedContinuationGroupBorel matchedContinuationGroupMeasurable matchedContinuationLocalField matchedContinuationQuotientMeasurable matchedContinuationUnipotentBorel matchedContinuationUnipotentMeasurable matchedContinuationValuativeRel matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel matchedShellFieldT2 matchedShellFieldTopology matchedShellGroupBorel matchedShellGroupMeasurable matchedShellGroupSecondCountable matchedShellGroupSigmaCompact matchedShellLocalField matchedShellQuotientLocallyCompact matchedShellQuotientMeasurable matchedShellQuotientSecondCountable matchedShellUnipotentBorel matchedShellUnipotentMeasurable matchedShellValuativeRel matrixWitnessFieldBorel matrixWitnessFieldMeasurable matrixWitnessFieldT2 matrixWitnessFieldTotallyDisconnected matrixWitnessGroupBorel matrixWitnessGroupMeasurable matrixWitnessLocalField matrixWitnessQuotientMeasurable matrixWitnessTopology matrixWitnessUnipotentBorel matrixWitnessUnipotentMeasurable matrixWitnessValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel nonempty_adjacentRankInvariantApproximation oppositeParabolicQuotientCompact productBoundFieldMeasurable productBoundGroupBorel productBoundGroupMeasurable productBoundLocalField productBoundModelAddCommGroup productBoundQuotientMeasurable productBoundTopology productBoundUnipotentBorel productBoundUnipotentMeasurable productBoundValuativeRel productsFieldTopology productsQuotientMeasurableSpace quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel scaledStandardCoefficientAsInverse sectionSurjectivityGLBorel sectionSurjectivityGLMeasurable sectionSurjectivityLocalField sectionSurjectivityT2 sectionSurjectivityTopology sectionSurjectivityValuativeRel setIntegral_matrixIntegrand_determinantSlice shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel spectralFieldTopology spectralFieldValuation spectralGroupBorelSpace spectralGroupMeasurableSpace spectralLocalField spectralQuotientBorelSpace spectralQuotientMeasurableSpace
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

local instance imageBoundFieldT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance imageBoundFieldTotallyDisconnected :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance imageBoundFieldMeasurable : MeasurableSpace F := borel _
local instance imageBoundFieldBorel : BorelSpace F := ⟨rfl⟩
local instance imageBoundGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance imageBoundGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance imageBoundUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F) := borel _
local instance imageBoundUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance imageBoundQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F) := borel _
local instance imageBoundQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

/-- Every actual rectangular Schwartz test is a finite sum of the separated
square/last-column tests used by the coefficient calculation. -/
theorem adjacentRankTest_exists_sum_separated {r : ℕ}
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F)) :
    ∃ (N : ℕ) (A : Fin N → GodementJacquet.MatrixTestFunction r F)
      (b : Fin N → SchwartzBruhat (Fin (r + 1) → F)),
      Φ = ∑ i, adjacentRankSeparatedTest (A i) (b i) := by
  let Φp := Hecke.TestFunction.pullback rectangularSplit.symm Φ
  obtain ⟨N, A, b, hab⟩ := SchwartzBruhat.exists_tensor_expansion Φp
  refine ⟨N, A, b, ?_⟩
  ext M
  have h := hab (rectangularFirstColumns M) (rectangularLastColumn M)
  simpa only [Φp, Hecke.TestFunction.pullback_apply, rectangularSplit_symm_apply,
    rectangularJoin_split, Submodule.coe_sum, Finset.sum_apply,
    adjacentRankSeparatedTest, Hecke.TestFunction.pullback_apply,
    rectangularSplit_apply, SchwartzBruhat.tensor_apply] using h

/-- At zero rows, the actual nested integral is exactly the corank integral. -/
theorem corankOneIntegral_eq_zeroZero {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Measure (LeftUnipotentQuotient r F)) (μ : AdditiveHaarMeasure F)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r) (s : ℂ) :
    corankOneIntegral ψ abv ν U W' s =
      unequalRankIntegralAt 0 0 rfl ψ abv ν (rectangularMeasure μ 0 (r + 1)) U W' s := by
  change corankOneIntegral ψ abv ν U W' s =
    unequalRankIntegral ψ abv 0 0 ν (rectangularMeasure μ 0 (r + 1)) U W' s
  rw [UnequalRankZeroRowAssembly.zero_row_integral_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q =>
    (unequalRankIntegrand_zero_zero ψ abv U W' s 0 q).symm

private theorem corankDenominatorBound_of_separated
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
    (P : Polynomial ℂ)
    (hlocal : ∀ (Φ : GodementJacquet.MatrixTestFunction r F)
      (φ : SchwartzBruhat (Fin (r + 1) → F))
      (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
      (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule),
      (∀ g, U.val.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
        (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g) →
      ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
      AdjacentRankCorankDenominatorBound F ψ ν U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) P) :
    ∀ (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
      (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
      AdjacentRankCorankDenominatorBound F ψ ν U.val
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) P := by
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
  intro U W' R hR
  let CL := (C.flip (scaledStandardCoefficientAsInverse F ψ τ ℓ' W')).comp Lmap
  have htests (Ψ : adjacentRankTestSpace ψ σ ℓ) :
      CL Ψ ∈ Submodule.span LaurentCoefficients
        {(algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹} := by
    induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
    | tmul Φ W =>
      obtain ⟨N, A, b, hΦ⟩ := adjacentRankTest_exists_sum_separated F Φ
      rw [hΦ, TensorProduct.sum_tmul, map_sum]
      apply Submodule.sum_mem
      intro i _
      exact hlocal (A i) (b i) W (Lmap (adjacentRankSeparatedTest (A i) (b i) ⊗ₜ[ℂ] W))
        (hL _) W' _ (hC _ W')
    | add Ψ Θ hΨ hΘ =>
      rw [map_add]
      exact Submodule.add_mem _ hΨ hΘ
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
  exact hvalue.symm ▸ htests Ψ

/-- The reciprocal polynomial bound on every actual pair of vectors in
specified nonzero original and inverse-character coefficient images. -/
def AdjacentRankModelCorankDenominatorBound
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    (ν : Measure (LeftUnipotentQuotient r F))
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F) VU)
    (J : glFunctionals ψ (r + 1) π)
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (P : Polynomial ℂ) : Prop :=
  ∀ (U : (glCoefficientModel ψ (r + 1) π J).toSubmodule)
    (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
    AdjacentRankCorankDenominatorBound F ψ ν U.val
      (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) P

/-- Whole-function image equality extends the actual separated finite-product
bound to every actual coefficient of the same induced functional. -/
theorem adjacentRankImage_productDenominatorBound
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
    (ℓ : glFunctionals ψ r σ) (hℓ : ℓ.val ≠ 0)
    (χ : Quasicharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F) VU)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (J : glFunctionals ψ (r + 1) π) (hJ : J.val ≠ 0)
    (himage : Set.range (adjacentRankModelMap F ψ μ hself σ ℓ χ hσ.1.1) =
      Set.range (fun v : π.asModule => fun g => J.val (π g v)))
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (P₀ P₁ : Polynomial ℂ)
    (hP₀ : IsPadicSymmetricLPolynomial F ψ μ σ τ P₀)
    (hP₁ : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) μ
      (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) τ)
      (rankOneCharacter 1) P₁) :
    AdjacentRankModelCorankDenominatorBound F ψ ν π J τ ℓ' (P₀ * P₁) := by
  apply corankDenominatorBound_of_separated F ψ μ hself ν hν σ hσ ℓ χ π hπ
    J hJ himage τ hτ ℓ' hℓ' (P₀ * P₁)
  intro Φ φ W U hU W'
  obtain ⟨φHat, hφ⟩ := (rowFourierCompatibility ψ μ (r + 1) hself).1 φ
  obtain ⟨N, B, hB⟩ := adjacentRankModel_matchedProductContinuation_exists
    F ψ μ hself σ hσ ℓ hℓ χ Φ φ φHat hφ W π hπ J hJ U hU τ hτ ℓ' hℓ' ν hν
  obtain ⟨f, M, MD, hM, -, hdata, -⟩ := hB W'
  exact adjacentRankProductContinuation_denominatorBound F ψ μ ν hν σ ℓ τ hτ
    ℓ' hℓ' W B U.val (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
    Φ φ χ f M 1 hM hdata P₀ P₁ hP₀ hP₁

/-- A bound on one nonzero coefficient image controls all functional images
by full Whittaker type, and has precisely the required polynomial direction. -/
theorem adjacentRankModelBound_polynomialDivisibility
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    {r : ℕ} [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F) VU)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (J : glFunctionals ψ (r + 1) π) (hJ : J.val ≠ 0)
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsPadicSymmetricLPolynomial F ψ μ π τ P)
    (hbound : AdjacentRankModelCorankDenominatorBound F ψ ν π J τ ℓ' A) :
    ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * A = Q * P := by
  let ℓinv := functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ'
  have hτinv : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ := by
    simpa only [standardCharacter_scale_neg_one] using hτ
  have hPair : IsPairLPolynomial qF ψ abv ν μ π τ P :=
    ((isPadicSymmetricLPolynomial_of_le (Nat.le_succ r)).mp hP).2 ν hν
  have hgen : IsNormalizedGenerator
      (unequalRankZetaValues qF ψ abv 0 0 ν (rectangularMeasure μ 0 (r + 1)) π τ) P :=
    (isPairLPolynomial_of_lt (Nat.lt_succ_self r)).mp hPair 0 0 rfl
  have hspan : zetaSpan
      (unequalRankZetaValues qF ψ abv 0 0 ν (rectangularMeasure μ 0 (r + 1)) π τ) ≤
      Submodule.span LaurentCoefficients
        {(algebraMap (Polynomial ℂ) RationalFunctions A)⁻¹} := by
    apply Submodule.span_le.mpr
    intro R hR
    rw [unequalRankZetaValues_eq_model qF ψ abv 0 0 ν (rectangularMeasure μ 0 (r + 1))
      J ℓinv (hπ.eq_smul hJ) (hτinv.eq_smul hℓ')] at hR
    obtain ⟨U, hU, W', hW', -, hcont⟩ := hR
    let U0 : (glCoefficientModel ψ (r + 1) π J).toSubmodule := ⟨U, hU⟩
    let W0inv : (coefficientModel τ ℓinv).toSubmodule := ⟨W', hW'⟩
    let W0 := inverseCoefficientAsScaledStandard F ψ τ ℓinv W0inv
    have hc : HasRationalContinuation qF
        (fun s => corankOneIntegral ψ abv ν U W' s) R :=
      RationalContinuationLinear.continuation_of_eq_on_right hcont
        ⟨0, fun s _ => corankOneIntegral_eq_zeroZero F ψ ν μ U W' s⟩
    exact hbound U0 W0 R hc
  apply (reciprocalLaurentSpanClearing P A hgen.polynomial_ne_zero hA).mp
  apply hspan
  rw [hgen.2]
  exact Submodule.subset_span rfl

end Langlands.AllField.RankinSelberg.Padic
