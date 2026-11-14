import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockGlobalAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockRowAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalAnalysis
/-! # Global convergence for the upper first-block disintegration -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding UpperSliceConverges continuous_diagonalIntegrand continuous_translated_unequalRankIntegrandAt continuous_upperAverage determinantWeight_firstBlockEmbedding determinantWeight_lowerRadical diagonalSupportGLTopological diagonalSupportT2 diagonalSupportTopology diagonalWhittaker_slice_hasCompactSupport disintegrationGLBorel disintegrationGLMeasurable disintegrationLocalField disintegrationMeasurable disintegrationQuotientMeasurable disintegrationTopology disintegrationUpperBorel disintegrationUpperMeasurable disintegrationValuation exists_rectangularSectionExpansion exists_uniformOrdinaryJacquetRealization firstBlockFiberIntegrand firstBlockRowJacobian firstBlockUpperCoefficient firstBlockUpperCoefficient_eq_small firstBlockUpperCoefficient_eq_small_of_whittakerType firstBlockUpperColumnNormProfile firstBlockUpperGlobalAverage firstBlockUpperRowAverage firstBlockUpperRowAverage_column_control firstBlockUpperRowAverage_eq firstBlockUpperRowAverage_joint_product_control firstBlockUpperRowAverage_joint_stronglyMeasurable firstBlockUpperValue firstBlockUpperValue_eq_rowScaled firstBlockUpperValue_fiber firstCoordinatesBorel firstCoordinatesLocalField firstCoordinatesMatrixBorel firstCoordinatesMeasurable firstCoordinatesSecondCountable firstCoordinatesTopology firstCoordinatesValuation firstFiberBorel firstFiberCountable firstFiberGLBorel firstFiberGLCountable firstFiberGLMeasurable firstFiberGLTopology firstFiberHBorel firstFiberHMeasurable firstFiberHQBorel firstFiberHQMeasurable firstFiberLocalField firstFiberMeasurable firstFiberMixedMeasurable firstFiberMixedSubgroupBorel firstFiberMixedSubgroupMeasurable firstFiberNBorel firstFiberNCountable firstFiberNMeasurable firstFiberNQBorel firstFiberNQMeasurable firstFiberT2 firstFiberTopology firstFiberValuation firstQuotientCountable firstQuotientGLBorel firstQuotientGLCountable firstQuotientGLMeasurable firstQuotientGLTopology firstQuotientHBorel firstQuotientHMeasurable firstQuotientHQBorel firstQuotientHQMeasurable firstQuotientLocalField firstQuotientMeasurable firstQuotientMixedMeasurable firstQuotientMixedSubgroupBorel firstQuotientMixedSubgroupMeasurable firstQuotientNBorel firstQuotientNCountable firstQuotientNMeasurable firstQuotientNQMeasurable firstQuotientT2 firstQuotientTopology firstQuotientValuation globalAnalysisBorel globalAnalysisCountable globalAnalysisGLBorel globalAnalysisGLCountable globalAnalysisGLMeasurable globalAnalysisGLTopology globalAnalysisHBorel globalAnalysisHMeasurable globalAnalysisHQBorel globalAnalysisHQMeasurable globalAnalysisLocalField globalAnalysisLowerMixedMeasurable globalAnalysisLowerMixedSubgroupBorel globalAnalysisLowerMixedSubgroupMeasurable globalAnalysisMeasurable globalAnalysisMixedBorel globalAnalysisMixedMeasurable globalAnalysisMixedSubgroupBorel globalAnalysisMixedSubgroupMeasurable globalAnalysisNBorel globalAnalysisNCountable globalAnalysisNMeasurable globalAnalysisNQBorel globalAnalysisNQMeasurable globalAnalysisT2 globalAnalysisTopology globalAnalysisValuation instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_firstBlockRowChange_iff integrable_firstBlockUpperValue_original_iff integrable_firstBlock_radical_product_ae integrable_rectangularBorelMeasure integral_firstBlockRowChange integral_firstBlockUpperValue integral_firstBlockUpperValue_columns integral_firstBlockUpperValue_original integral_norm_firstBlockUpperValue_columns integral_norm_firstBlockUpperValue_original integrandBridgeMeasurable integrandBridgeTopology quotientDeterminantWeight quotientDeterminantWeight_continuous quotientDeterminantWeight_mk radicalUnfoldingBorel radicalUnfoldingCountable radicalUnfoldingGLBorel radicalUnfoldingGLCountable radicalUnfoldingGLMeasurable radicalUnfoldingGLTopology radicalUnfoldingHBorel radicalUnfoldingHMeasurable radicalUnfoldingHQMeasurable radicalUnfoldingLocalField radicalUnfoldingMeasurable radicalUnfoldingNBorel radicalUnfoldingNCountable radicalUnfoldingNMeasurable radicalUnfoldingNQMeasurable radicalUnfoldingT2 radicalUnfoldingTopology radicalUnfoldingValuation rectangleChangeMeasurable rectangleChangeTopology rectangleUnfoldingCountable rectangleUnfoldingGLBorel rectangleUnfoldingGLCountable rectangleUnfoldingGLMeasurable rectangleUnfoldingGLTopology rectangleUnfoldingHBorel rectangleUnfoldingHMeasurable rectangleUnfoldingHQMeasurable rectangleUnfoldingLocalField rectangleUnfoldingMeasurable rectangleUnfoldingNBorel rectangleUnfoldingNCountable rectangleUnfoldingNMeasurable rectangleUnfoldingNQMeasurable rectangleUnfoldingT2 rectangleUnfoldingTopology rectangleUnfoldingValuation rectangularBorelMeasure rectangularMeasure_map_firstBlockRowChange rectangularSectionAverage rectangularSectionAverage_firstBlock_unfolding rectangularSectionIntegrand rectangularSectionIntegrand_expansion rectangularSectionIntegrand_integrable rectangularSectionIntegrand_mk rectangularSectionIntegrand_regular rectangularSectionNormProfile rectangularSection_firstBlock_product_fibers rectangularSection_slice_unfolding rectangularWhittaker rectangularWhittaker_apply rowAnalysisGLTopology rowAnalysisLocalField rowAnalysisMeasurable rowAnalysisTopology rowAnalysisValuation sectionAverage_mk sectionAverages_continuous sectionIntegrand sectionIntegrand_continuous sectionIntegrand_fiberPoint sectionIntegrand_mk sectionIntegrand_slice_unfolding sectionNormAverage_mk sectionUnfoldingBorel sectionUnfoldingCountable sectionUnfoldingGLBorel sectionUnfoldingGLCountable sectionUnfoldingGLLocalCompact sectionUnfoldingGLMeasurable sectionUnfoldingGLTopology sectionUnfoldingHBorel sectionUnfoldingHMeasurable sectionUnfoldingHQBorel sectionUnfoldingHQMeasurable sectionUnfoldingLocalField sectionUnfoldingMeasurable sectionUnfoldingNBorel sectionUnfoldingNCountable sectionUnfoldingNMeasurable sectionUnfoldingNQBorel sectionUnfoldingNQMeasurable sectionUnfoldingT2 sectionUnfoldingTopology sectionUnfoldingValuation unequalRankIntegrandAt_mk unequalRankMatrix_rectangle_change unequalRankSliceCoefficientAt_eq_integral upperSliceConverges upperSliceConvergesAt
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockFirstBlockQuotientIntegration twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding FirstBlockKernelAnalysisStatement MixedQuotient NormOneRightInvariant NormalizedTowerStatement analytic_of_comp_eq blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint continuous_mixedFirstQuotient determinantOrder determinantOrder_mixedLeftShift determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding exists_determinantOrder fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberKernel fiberKernel_comp_zeroSlice_eq fiberKernel_comp_zeroSlice_eq_zeroKernel_comp_slice fiberKernel_compact_ne_top fiberKernel_eq_zero_shift fiberKernel_isSFinite fiberKernel_mk fiberKernel_zero_comp fiberKernel_zero_comp_restrict fiberMeasures_mixedSubgroup_mul fiberPoint_firstBlockEmbedding_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul fiberPoint_slice_isCompact_preimage firstBlockAverage firstBlockAverage_eq_integral_kernel firstBlockAverage_mk firstBlockEmbedding_mem_mixedSubgroup instBorelSpaceBlockQuotientCarrier instBorelSpaceBlockQuotientCarrier_1 instBorelSpaceGeneralLinearCarrier instBorelSpaceGeneralLinearCarrier_1 instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLeftUnipotentQuotientCarrier_1 instBorelSpaceMixedQuotient instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instBorelSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier_1 instLocallyCompactSpaceMatrixFinCarrier instLocallyCompactSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instLocallyCompactSpaceSubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceBlockQuotientCarrier instMeasurableSpaceBlockQuotientCarrier_1 instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceGeneralLinearCarrier_1 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier_1 instMeasurableSpaceMixedQuotient instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupNormOneSubgroup instMeasurableSpaceSubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupMixedSubgroup instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologyGeneralLinearCarrier_2 instSecondCountableTopologySubtypeGeneralLinearCarrierMemSubgroupUpperUnipotent instSecondCountableTopologySubtypeGeneralLinearHAddNatOfNatFinCarrierMemSubgroupNormOneSubgroup instT2SpaceCarrier instT2SpaceCarrier_1 instT2SpaceCarrier_2 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 isClopen_determinantSlice isClosed_mixedSubgroup isOpenEmbedding_normOneSubtype kernelShiftBlockQuotientBorel kernelShiftBlockQuotientMeasurable kernelShiftGLBorel kernelShiftGLMeasurable kernelShiftLocalField kernelShiftMixedBorel kernelShiftMixedMeasurable kernelShiftMixedQuotientBorel kernelShiftMixedQuotientMeasurable kernelShiftSmallQuotientBorel kernelShiftSmallQuotientMeasurable kernelShiftTopology kernelShiftUnipotentBorel kernelShiftUnipotentMeasurable kernelShiftValuativeRel lintegral_blockHaar lintegral_comp_quotientAverageReal lintegral_fiberPoint_quotientAverageReal map_mixedHaar_conjugation map_normOneHaar map_normOneHaar_conjugation map_restrict_mixedLeftShift map_restrict_smallSlice map_restrict_smallSlice_of_ord measurableSet_determinantSlice measurable_fiberMeasures measurePreserving_mixedLeftShift mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedFirstQuotient mixedFirstQuotient_block_mul mixedHaar mixedHaar_isHaar mixedHaar_isMulRightInvariant mixedHaar_regular mixedLeftShift mixedLeftShift_mk mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mixed_compatibleMeasureExists mk_mem_determinantSlice mul_inv_mem_normOne_of_ord_eq normOneHaar normOneHaar_isHaar normOneHaar_isMulRightInvariant normOneHaar_regular normOneRightInvariant_of_isCompatible normOneSubgroup normalized_tower ord_determinant_eq_zero rightTranslate_mem_determinantSlice sliceShiftFieldT2 sliceShiftGLBorel sliceShiftGLLocallyCompact sliceShiftGLMeasurable sliceShiftGLSecondCountable sliceShiftLocalField sliceShiftMixedBorel sliceShiftMixedLocallyCompact sliceShiftMixedMeasurable sliceShiftMixedQuotientBorel sliceShiftMixedQuotientMeasurable sliceShiftNormOneBorel sliceShiftNormOneLocallyCompact sliceShiftNormOneMeasurable sliceShiftNormOneSecondCountable sliceShiftTopology sliceShiftUnipotentBorel sliceShiftUnipotentLocallyCompact sliceShiftUnipotentMeasurable sliceShiftUnipotentSecondCountable sliceShiftValuativeRel small_orbitKernel_comp_zero towerBlockQuotientLocallyCompact towerBlockQuotientSecondCountable towerBlockQuotientT2 towerInst1 towerInst10 towerInst11 towerInst12 towerInst13 towerInst14 towerInst15 towerInst16 towerInst17 towerInst2 towerInst20 towerInst21 towerInst23 towerInst24 towerInst25 towerInst26 towerInst27 towerInst28 towerInst29 towerInst3 towerInst30 towerInst4 towerInst8 towerInst9 unfoldingInst1 unfoldingInst10 unfoldingInst11 unfoldingInst12 unfoldingInst13 unfoldingInst14 unfoldingInst15 unfoldingInst2 unfoldingInst20 unfoldingInst21 unfoldingInst23 unfoldingInst24 unfoldingInst3 unfoldingInst4 unfoldingInst8 unfoldingInst9
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient RadicalIntegrationStatement RadicalTowerStatement continuous_determinantOrder continuous_firstBlockFiberPoint continuous_lowerMixedFirstQuotient continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint continuous_rightRadicalCoord determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberMeasures_lowerMixed_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk firstBlockFiberPoint_slice_isCompact_preimage firstBlockKernel firstBlockKernel_compact_ne_top firstBlockKernel_isSFinite firstBlockKernel_mk iUnion_determinantSlice instBorelSpaceCarrier instBorelSpaceCarrier_1 instBorelSpaceGeneralLinearCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceLeftUnipotentQuotientCarrier_1 instBorelSpaceLowerMixedQuotient instBorelSpaceLowerQuotientCarrier instBorelSpaceLowerQuotientCarrier_1 instBorelSpaceMixedQuotient instBorelSpaceMixedQuotient_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instLocallyCompactSpaceGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier_1 instLocallyCompactSpaceMatrixFinCarrier instMeasurableSpaceCarrier instMeasurableSpaceCarrier_1 instMeasurableSpaceGeneralLinearCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier_1 instMeasurableSpaceLowerMixedQuotient instMeasurableSpaceLowerQuotientCarrier instMeasurableSpaceLowerQuotientCarrier_1 instMeasurableSpaceMixedQuotient instMeasurableSpaceMixedQuotient_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instSecondCountableTopologyGeneralLinearCarrier instSecondCountableTopologyGeneralLinearCarrier_1 instSecondCountableTopologyMatrixFinCarrier instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lintegral_mixedHaar_radical lintegral_radicalFiberPoint_quotientAverageReal lintegral_radicalKernel_comp_quotientAverageReal lowerBlockUnipotent_le_lowerMixedSubgroup lowerMeasuresInstance01 lowerMeasuresInstance02 lowerMeasuresInstance03 lowerMeasuresInstance04 lowerMeasuresInstance05 lowerMeasuresInstance06 lowerMeasuresInstance07 lowerMeasuresInstance08 lowerMeasuresInstance09 lowerMeasuresInstance10 lowerMeasuresInstance13 lowerMeasuresInstance14 lowerMeasuresInstance15 lowerMeasuresInstance16 lowerMeasuresInstance17 lowerMeasuresInstance18 lowerMeasuresInstance19 lowerMeasuresInstance20 lowerMeasuresInstance21 lowerMeasuresInstance22 lowerMeasuresInstance23 lowerMeasuresInstance24 lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedFirstQuotient lowerMixedFirstQuotient_lower_mul lowerMixedHaar lowerMixedHaar_integral lowerMixedHaar_isHaar lowerMixedHaar_isMulRightInvariant lowerMixedHaar_regular lowerMixedIntegralOpen lowerMixedIntegralOpen_isCompact lowerMixedProductMeasure lowerMixedProductMeasure_eq_smul lowerMixedProductMeasure_isHaar lowerMixedProductMeasure_isMulLeftInvariant lowerMixedProductMeasure_isMulRightInvariant lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_compatibleMeasureExists lowerMixed_decomposition lowerMixed_preimage_integral lowerNormalizationInstance01 lowerNormalizationInstance02 lowerNormalizationInstance03 lowerNormalizationInstance04 lowerNormalizationInstance05 lowerNormalizationInstance06 lowerNormalizationInstance07 lowerNormalizationInstance08 lowerNormalizationInstance10 lowerNormalizationInstance11 lowerNormalizationInstance12 lowerNormalizationInstance13 lowerNormalizationInstance14 lowerNormalizationInstance15 lowerNormalizationInstance16 lowerNormalizationInstance17 lowerNormalizationInstance18 lowerNormalizationInstance19 lowerNormalizationInstance20 lowerNormalizationInstance21 lowerNormalizationInstance22 lowerNormalizationInstance23 lowerNormalizationInstance24 lowerNormalizationInstance25 lowerNormalizationInstance26 lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadicalAnalysisInstance01 lowerRadicalAnalysisInstance02 lowerRadicalAnalysisInstance03 lowerRadicalAnalysisInstance05 lowerRadicalAnalysisInstance06 lowerRadicalAnalysisInstance07 lowerRadicalAnalysisInstance10 lowerRadicalAnalysisInstance11 lowerRadicalAnalysisInstance12 lowerRadicalAnalysisInstance23 lowerRadicalAnalysisInstance24 lowerRadicalAnalysisInstance27 lowerRadicalAnalysisInstance28 lowerRadicalAnalysisInstance31 lowerRadicalAnalysisInstance32 lowerRadicalAnalysisInstance36 lowerRadicalTowerInstance01 lowerRadicalTowerInstance02 lowerRadicalTowerInstance03 lowerRadicalTowerInstance04 lowerRadicalTowerInstance05 lowerRadicalTowerInstance06 lowerRadicalTowerInstance07 lowerRadicalTowerInstance08 lowerRadicalTowerInstance09 lowerRadicalTowerInstance10 lowerRadicalTowerInstance11 lowerRadicalTowerInstance12 lowerRadicalTowerInstance13 lowerRadicalTowerInstance14 lowerRadicalTowerInstance15 lowerRadicalTowerInstance16 lowerRadicalTowerInstance17 lowerRadicalTowerInstance18 lowerRadicalTowerInstance19 lowerRadicalTowerInstance20 lowerRadicalTowerInstance21 lowerRadicalTowerInstance22 lowerRadicalTowerInstance23 lowerRadicalTowerInstance24 lowerRadicalTowerInstance27 lowerRadicalTowerInstance28 lowerRadicalTowerInstance31 lowerRadicalTowerInstance32 lowerRadicalTowerInstance33 lowerRadicalTowerInstance34 lowerRadicalTowerInstance35 lowerRadicalTowerInstance36 lowerRadicalTowerInstance37 lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurable_firstBlockFiberMeasures measurable_radicalFiberMeasures measurePreserving_radicalChange mem_determinantSlice mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice normOneHaar_integral pairwise_disjoint_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_eq_integral_radicalKernel radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberMeasures_lowerMixed_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_isCompact_preimage radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff radicalIntegration radicalKernel radicalKernel_comp radicalKernel_comp_restrict radicalKernel_compact_ne_top radicalKernel_isSFinite radicalKernel_mk radicalTower rightRadicalCoord rightRadicalCoord_mixed_mul_radical rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding dualIntegrand_integrableOn_slice dualSmallIntegral_series firstBlockCoefficient firstBlockCoefficient_apply firstBlockCoefficient_lowerRadical_mul inv_leviHalfModulus_blockPair_one scalarSection_firstBlockEmbedding_mul scalarSection_lowerRadical_mul smallIntegral_series smallIntegrand_integrableOn_slice tensorContraction_blockTensor_blockPair_one unequalRankIntegrandAt unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient unequalRankSliceCoefficientAt unequalRank_sliceExpansion
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent hiding unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped ENNReal

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance globalAnalysisT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance globalAnalysisCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance globalAnalysisGLTopology (a : ℕ) : IsTopologicalGroup (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup a
local instance globalAnalysisGLCountable (a : ℕ) : SecondCountableTopology (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology a
local instance globalAnalysisMeasurable : MeasurableSpace F := borel _
local instance globalAnalysisBorel : BorelSpace F := ⟨rfl⟩
local instance globalAnalysisGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F) := borel _
local instance globalAnalysisGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F) := ⟨rfl⟩
local instance globalAnalysisNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F) := borel _
local instance globalAnalysisNBorel (a : ℕ) : BorelSpace (upperUnipotent a F) := ⟨rfl⟩
local instance globalAnalysisNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance globalAnalysisNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F) := borel _
local instance globalAnalysisNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable {ψ : UnitaryAdditiveCharacter F}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F)

/-- The upper first-block coefficient integrated over the remaining external
second-block columns, with the actual supplied quotient and rectangle measures. -/
def firstBlockUpperGlobalAverage
    (μ : Measure (LeftUnipotentQuotient (m 0) F)) (d : ℤ)
    (g : GeneralLinear (t + 1) F) : ℂ :=
  ∫ Y, firstBlockUpperCoefficient F h j k ell f Wtest ν μ d Y g
    ∂rectangularMeasure ν j (m 1 + 1)

local instance globalAnalysisHQMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) := borel _
local instance globalAnalysisHQBorel :
    BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) := ⟨rfl⟩
local instance globalAnalysisHMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h F) := borel _
local instance globalAnalysisHBorel :
    BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h F) := ⟨rfl⟩
local instance globalAnalysisMixedSubgroupMeasurable :
    MeasurableSpace (mixedSubgroup F h) := borel _
local instance globalAnalysisMixedSubgroupBorel : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance globalAnalysisLowerMixedSubgroupMeasurable :
    MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance globalAnalysisLowerMixedSubgroupBorel : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance globalAnalysisMixedMeasurable :
    MeasurableSpace (MixedQuotient F h) := borel _
local instance globalAnalysisMixedBorel : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance globalAnalysisLowerMixedMeasurable :
    MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance globalAnalysisLowerMixedBorel : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

/-- Joint measurability retains the radical, small quotient and remaining
external columns. No measurable quotient representative is chosen. -/
theorem firstBlockUpperRowAverage_joint_stronglyMeasurable
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0)) (s : ℂ)
    (g : GeneralLinear (t + 1) F) :
    StronglyMeasurable (fun z :
        (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
          LeftUnipotentQuotient (m 0) F) ×
            Matrix (Fin j) (Fin (m 1 + 1)) F =>
      firstBlockUpperRowAverage F h j k ell f Wtest ν s z.1.2 z.1.1 z.2 g) := by
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hsmall : Continuous (firstBlockCoefficient ell f g).val.val := by
    obtain ⟨v, hv⟩ := modelMap_surjective (σ 0) (ell 0) (firstBlockCoefficient ell f g)
    rw [← hv]
    exact (matrixCoefficient_isLocallyConstant (σ 0) (ell 0).val v (hσ v)).continuous
  have hi := (continuous_translated_unequalRankIntegrandAt F (m 1 + 1 + j) k
    (firstBlockSmallRank h j k) ψ Wtest (firstBlockCoefficient ell f g).val
    hW hsmall s).measurable.stronglyMeasurable
  have hcols : Measurable (fun Y : Matrix (Fin j) (Fin (m 1 + 1)) F =>
      firstBlockColumns h j (0 : Matrix (Fin j) (Fin (m 0 + 1)) F) Y) := by
    simpa only [Function.comp_def, id_eq, firstBlockColumnJoinEquiv_apply] using
      (firstBlockColumnJoinEquiv F h j).measurable.comp
        ((measurable_const (a := (0 : Matrix (Fin j) (Fin (m 0 + 1)) F))).prodMk
          measurable_id)
  have htrans : Measurable (fun Y : Matrix (Fin j) (Fin (m 1 + 1)) F =>
      rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
        appendIdentity t (j + k + 1) g) :=
    ((continuous_rectangularUnipotent j k).measurable.comp hcols).mul_const _
  have hrows : Measurable (fun z :
        Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
          Matrix (Fin j) (Fin (m 0 + 1)) F =>
      firstBlockRows j z.1 z.2) := by
    simpa only [Function.comp_def, id_eq, firstBlockRowJoinEquiv_apply, firstBlockRows] using
      (firstBlockRowJoinEquiv F (m 0 + 1) (m 1 + 1) j).measurable.comp
        (measurable_fst.prodMk measurable_snd)
  have hm := hi.comp_measurable
    (measurable_fst.fst.snd.prodMk
      ((hrows.comp (measurable_fst.fst.fst.prodMk measurable_snd)).prodMk
        (htrans.comp measurable_fst.snd)))
  have ha := hm.integral_prod_right' (ν := rectangularMeasure ν j (m 0 + 1))
  simpa only [firstBlockUpperRowAverage_eq, Function.comp_def] using
    ha.const_mul (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
      (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)))

/-- The original raw norm on the actual radical/quotient product controls the
three-variable row average and justifies moving the remaining columns outside. -/
theorem firstBlockUpperRowAverage_joint_product_control
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0)) (s : ℂ)
    (μZ : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)) [SFinite μZ]
    (μ : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite μ]
    (g : GeneralLinear (t + 1) F)
    (hrect : ∀ᵐ z ∂μZ.prod μ, Integrable
      (fun x => rectangularSectionIntegrand F ell f j k Wtest
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)) x
        (fiberPoint h F z.2 (lowerRadical h F z.1 * g)))
      (rectangularMeasure ν j (t + 1)))
    (hN : Integrable (fun z =>
      rectangularSectionNormProfile F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (fiberPoint h F z.2 (lowerRadical h F z.1 * g))) (μZ.prod μ)) :
    Integrable (fun z :
        (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
          LeftUnipotentQuotient (m 0) F) ×
            Matrix (Fin j) (Fin (m 1 + 1)) F =>
      firstBlockUpperRowAverage F h j k ell f Wtest ν s z.1.2 z.1.1 z.2 g)
      ((μZ.prod μ).prod (rectangularMeasure ν j (m 1 + 1))) ∧
    (∫ Z, ∫ q, rectangularSectionAverage F ell f j k Wtest ν
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
      (fiberPoint h F q (lowerRadical h F Z * g)) ∂μ ∂μZ) =
      ∫ Y, ∫ Z, ∫ q, firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g
        ∂μ ∂μZ ∂rectangularMeasure ν j (m 1 + 1) := by
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hm := firstBlockUpperRowAverage_joint_stronglyMeasurable
    F h j k ell f Wtest ν hW hσ s g
  have hp : Integrable (fun z =>
      firstBlockUpperColumnNormProfile F h j k ell f Wtest ν s z.2 z.1 g)
      (μZ.prod μ) := by
    apply hN.mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hrect] with z hz
    have hn : 0 ≤ firstBlockUpperColumnNormProfile F h j k ell f Wtest ν s z.2 z.1 g :=
      integral_nonneg (fun _ => norm_nonneg _)
    change ‖firstBlockUpperColumnNormProfile F h j k ell f Wtest ν s z.2 z.1 g‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact (firstBlockUpperRowAverage_column_control
      F h j k ell f Wtest ν s z.2 z.1 g hz).2.1
  have hi : Integrable (fun z :
        (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
          LeftUnipotentQuotient (m 0) F) ×
            Matrix (Fin j) (Fin (m 1 + 1)) F =>
      firstBlockUpperRowAverage F h j k ell f Wtest ν s z.1.2 z.1.1 z.2 g)
      ((μZ.prod μ).prod (rectangularMeasure ν j (m 1 + 1))) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨?_, hp⟩
    filter_upwards [hrect] with z hz
    exact (firstBlockUpperRowAverage_column_control
      F h j k ell f Wtest ν s z.2 z.1 g hz).1
  have he := Measure.ae_ae_of_ae_prod hrect
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ Z, ∫ q, ∫ Y,
        firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g
          ∂rectangularMeasure ν j (m 1 + 1) ∂μ ∂μZ := by
      apply integral_congr_ae
      filter_upwards [he] with Z hZ
      apply integral_congr_ae
      filter_upwards [hZ] with q hq
      exact (firstBlockUpperRowAverage_column_control
        F h j k ell f Wtest ν s q Z g hq).2.2.symm
    _ = ∫ z, ∫ Y,
        firstBlockUpperRowAverage F h j k ell f Wtest ν s z.2 z.1 Y g
          ∂rectangularMeasure ν j (m 1 + 1) ∂μZ.prod μ :=
      (integral_prod _ hi.integral_prod_left).symm
    _ = ∫ Y, ∫ z,
        firstBlockUpperRowAverage F h j k ell f Wtest ν s z.2 z.1 Y g
          ∂μZ.prod μ ∂rectangularMeasure ν j (m 1 + 1) :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hi.prod_left_ae] with Y hY
      exact integral_prod _ hY

/-- Composing the exact first-block and radical towers gives genuine
integrability on the actual radical/small-quotient product almost everywhere
on the lower mixed zero slice. This applies to any measurable raw profile. -/
theorem integrable_firstBlock_radical_product_ae
    (N : TwoBlockUnipotentQuotient.BlockQuotient h F → ℝ) (hNm : Measurable N)
    (μZ : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F))
    [μZ.IsAddHaarMeasure] [SFinite μZ]
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F))
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SigmaFinite νA]
    (νM : Measure (MixedQuotient F h)) (νL : Measure (LowerMixedQuotient F h))
    (hνH : IsCompatible (TwoBlockUnipotentQuotient.blockUnipotent h F)
      (generalLinearHaar F t) (TwoBlockUnipotentQuotient.blockHaar F h) νH)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)
    (hνM : IsCompatible (mixedSubgroup F h) (generalLinearHaar F t)
      (mixedHaar F h) νM)
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F t)
      (lowerMixedHaar F h) νL)
    (d : ℤ)
    (hNi : Integrable N
      (νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h d))) :
    ∀ᵐ qbase ∂νL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0),
      ∀ g : GeneralLinear (t + 1) F, qbase = Quotient.mk _ g →
        Integrable (fun z :
            Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
              LeftUnipotentQuotient (m 0) F =>
          N (fiberPoint h F z.2 (lowerRadical h F z.1 * g)))
          (μZ.prod (νA.restrict
            (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d))) := by
  let hInv := normOneRightInvariant_of_isCompatible F (m 0)
    (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA hνA
  let κA := fiberKernel F h νA hInv d
  let κR := radicalKernel F h μZ
  let μL := νL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)
  let μA := νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d)
  let c := μZ {Z | ∀ i j, Z i j ∈ Valuation.integer (ValuativeRel.valuation F)}
  have hzero := (normalized_tower F h νA hInv hνA νM hνM νH hνH).2
  have hcompA := fiberKernel_comp_zeroSlice_eq F h νA hInv hνA νM hνM νH hzero d
  have hcompR := (radicalTower F h μZ νL hνL νM hνM).2 0
  have hcomp : (κA ∘ₖ κR) ∘ₘ μL =
      c • νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h d) := by
    rw [← Measure.comp_assoc, hcompR, Measure.comp_smul, hcompA]
  have hc := Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.integerCube_mass_pos_lt_top F
    (m 1 + 1) (m 0 + 1) μZ
  have hNc : Integrable N ((κA ∘ₖ κR) ∘ₘ μL) := by
    rw [hcomp]
    exact hNi.smul_measure hc.2.ne
  have hNae := ((Measure.integrable_comp_iff hNm.aestronglyMeasurable).mp hNc).1
  filter_upwards [hNae] with qbase hq g hqg
  subst qbase
  have hfmR : Measurable (fun Z => radicalFiberPoint F h Z g) :=
    ((continuous_radicalFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  have hNcR : Integrable N (κA ∘ₘ κR (Quotient.mk _ g)) := by
    simpa only [Kernel.comp_apply] using hq
  obtain ⟨hNfiber, hNnorm⟩ :=
    (Measure.integrable_comp_iff hNm.aestronglyMeasurable).mp hNcR
  rw [radicalKernel_mk] at hNfiber hNnorm
  have hNfiberZ := ae_of_ae_map hfmR.aemeasurable hNfiber
  have hNnormZ := hNnorm.comp_measurable hfmR
  have hfmA (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F) :
      Measurable (fun q : LeftUnipotentQuotient (m 0) F =>
        fiberPoint h F q (lowerRadical h F Z * g)) :=
    ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  have hfm : Measurable (fun z :
        Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
          LeftUnipotentQuotient (m 0) F =>
      fiberPoint h F z.2 (lowerRadical h F z.1 * g)) :=
    (continuous_fiberPoint F h).measurable.comp
      (measurable_snd.prodMk
        (((continuous_lowerRadical h F).measurable.comp measurable_fst).mul_const g))
  apply (integrable_prod_iff (hNm.comp hfm).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hNfiberZ] with Z hZ
    rw [radicalFiberPoint_def, fiberKernel_mk] at hZ
    exact hZ.comp_measurable (hfmA Z)
  · convert hNnormZ using 1
    funext Z
    dsimp only [Function.comp_def]
    rw [radicalFiberPoint_def, fiberKernel_mk]
    exact (integral_map (hfmA Z).aemeasurable hNm.norm.aestronglyMeasurable).symm

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
