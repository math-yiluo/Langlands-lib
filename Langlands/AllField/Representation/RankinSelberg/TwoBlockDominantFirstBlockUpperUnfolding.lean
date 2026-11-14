import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockUpperUnfolding
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockGlobalAnalysis
/-! # The actual global upper first-block unfolding -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding UpperSliceConverges continuous_diagonalIntegrand continuous_translated_unequalRankIntegrandAt continuous_upperAverage determinantWeight_firstBlockEmbedding determinantWeight_lowerRadical diagonalSupportGLTopological diagonalSupportT2 diagonalSupportTopology diagonalWhittaker_slice_hasCompactSupport disintegrationGLBorel disintegrationGLMeasurable disintegrationLocalField disintegrationMeasurable disintegrationQuotientMeasurable disintegrationTopology disintegrationUpperBorel disintegrationUpperMeasurable disintegrationValuation exists_rectangularSectionExpansion exists_uniformOrdinaryJacquetRealization firstBlockFiberIntegrand firstBlockRowJacobian firstBlockUpperCoefficient firstBlockUpperCoefficient_eq_small firstBlockUpperCoefficient_eq_small_of_whittakerType firstBlockUpperColumnNormProfile firstBlockUpperGlobalAverage firstBlockUpperQuotientAverage firstBlockUpperQuotientAverage_analysis firstBlockUpperQuotientAverage_integral_eq_large firstBlockUpperRowAverage firstBlockUpperRowAverage_column_control firstBlockUpperRowAverage_eq firstBlockUpperRowAverage_joint_product_control firstBlockUpperRowAverage_joint_stronglyMeasurable firstBlockUpperValue firstBlockUpperValue_eq_rowScaled firstBlockUpperValue_fiber firstCoordinatesBorel firstCoordinatesLocalField firstCoordinatesMatrixBorel firstCoordinatesMeasurable firstCoordinatesSecondCountable firstCoordinatesTopology firstCoordinatesValuation firstFiberBorel firstFiberCountable firstFiberGLBorel firstFiberGLCountable firstFiberGLMeasurable firstFiberGLTopology firstFiberHBorel firstFiberHMeasurable firstFiberHQBorel firstFiberHQMeasurable firstFiberLocalField firstFiberMeasurable firstFiberMixedMeasurable firstFiberMixedSubgroupBorel firstFiberMixedSubgroupMeasurable firstFiberNBorel firstFiberNCountable firstFiberNMeasurable firstFiberNQBorel firstFiberNQMeasurable firstFiberT2 firstFiberTopology firstFiberValuation firstQuotientCountable firstQuotientGLBorel firstQuotientGLCountable firstQuotientGLMeasurable firstQuotientGLTopology firstQuotientHBorel firstQuotientHMeasurable firstQuotientHQBorel firstQuotientHQMeasurable firstQuotientLocalField firstQuotientMeasurable firstQuotientMixedMeasurable firstQuotientMixedSubgroupBorel firstQuotientMixedSubgroupMeasurable firstQuotientNBorel firstQuotientNCountable firstQuotientNMeasurable firstQuotientNQMeasurable firstQuotientT2 firstQuotientTopology firstQuotientValuation globalAnalysisBorel globalAnalysisCountable globalAnalysisGLBorel globalAnalysisGLCountable globalAnalysisGLMeasurable globalAnalysisGLTopology globalAnalysisHBorel globalAnalysisHMeasurable globalAnalysisHQBorel globalAnalysisHQMeasurable globalAnalysisLocalField globalAnalysisLowerMixedMeasurable globalAnalysisLowerMixedSubgroupBorel globalAnalysisLowerMixedSubgroupMeasurable globalAnalysisMeasurable globalAnalysisMixedBorel globalAnalysisMixedMeasurable globalAnalysisMixedSubgroupBorel globalAnalysisMixedSubgroupMeasurable globalAnalysisNBorel globalAnalysisNCountable globalAnalysisNMeasurable globalAnalysisNQBorel globalAnalysisNQMeasurable globalAnalysisT2 globalAnalysisTopology globalAnalysisValuation instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_firstBlockRowChange_iff integrable_firstBlockUpperValue_original_iff integrable_firstBlock_radical_product_ae integrable_rectangularBorelMeasure integral_firstBlockRowChange integral_firstBlockUpperValue integral_firstBlockUpperValue_columns integral_firstBlockUpperValue_original integral_norm_firstBlockUpperValue_columns integral_norm_firstBlockUpperValue_original integrandBridgeMeasurable integrandBridgeTopology quotientDeterminantWeight quotientDeterminantWeight_continuous quotientDeterminantWeight_mk radicalUnfoldingBorel radicalUnfoldingCountable radicalUnfoldingGLBorel radicalUnfoldingGLCountable radicalUnfoldingGLMeasurable radicalUnfoldingGLTopology radicalUnfoldingHBorel radicalUnfoldingHMeasurable radicalUnfoldingHQMeasurable radicalUnfoldingLocalField radicalUnfoldingMeasurable radicalUnfoldingNBorel radicalUnfoldingNCountable radicalUnfoldingNMeasurable radicalUnfoldingNQMeasurable radicalUnfoldingT2 radicalUnfoldingTopology radicalUnfoldingValuation rectangleChangeMeasurable rectangleChangeTopology rectangleUnfoldingCountable rectangleUnfoldingGLBorel rectangleUnfoldingGLCountable rectangleUnfoldingGLMeasurable rectangleUnfoldingGLTopology rectangleUnfoldingHBorel rectangleUnfoldingHMeasurable rectangleUnfoldingHQMeasurable rectangleUnfoldingLocalField rectangleUnfoldingMeasurable rectangleUnfoldingNBorel rectangleUnfoldingNCountable rectangleUnfoldingNMeasurable rectangleUnfoldingNQMeasurable rectangleUnfoldingT2 rectangleUnfoldingTopology rectangleUnfoldingValuation rectangularBorelMeasure rectangularMeasure_map_firstBlockRowChange rectangularSectionAverage rectangularSectionAverage_firstBlock_unfolding rectangularSectionIntegrand rectangularSectionIntegrand_expansion rectangularSectionIntegrand_integrable rectangularSectionIntegrand_mk rectangularSectionIntegrand_regular rectangularSectionNormProfile rectangularSection_firstBlock_product_fibers rectangularSection_slice_unfolding rectangularWhittaker rectangularWhittaker_apply rectangular_integerCube_mass_swap rowAnalysisGLTopology rowAnalysisLocalField rowAnalysisMeasurable rowAnalysisTopology rowAnalysisValuation sectionAverage_mk sectionAverages_continuous sectionIntegrand sectionIntegrand_continuous sectionIntegrand_fiberPoint sectionIntegrand_mk sectionIntegrand_slice_unfolding sectionNormAverage_mk sectionUnfoldingBorel sectionUnfoldingCountable sectionUnfoldingGLBorel sectionUnfoldingGLCountable sectionUnfoldingGLLocalCompact sectionUnfoldingGLMeasurable sectionUnfoldingGLTopology sectionUnfoldingHBorel sectionUnfoldingHMeasurable sectionUnfoldingHQBorel sectionUnfoldingHQMeasurable sectionUnfoldingLocalField sectionUnfoldingMeasurable sectionUnfoldingNBorel sectionUnfoldingNCountable sectionUnfoldingNMeasurable sectionUnfoldingNQBorel sectionUnfoldingNQMeasurable sectionUnfoldingT2 sectionUnfoldingTopology sectionUnfoldingValuation unequalRankIntegrandAt_mk unequalRankMatrix_rectangle_change unequalRankSliceCoefficientAt_eq_integral upperSliceConverges upperSliceConvergesAt upperUnfoldingBorel upperUnfoldingCountable upperUnfoldingGLBorel upperUnfoldingGLCountable upperUnfoldingGLMeasurable upperUnfoldingGLTopology upperUnfoldingHBorel upperUnfoldingHMeasurable upperUnfoldingHQMeasurable upperUnfoldingLocalField upperUnfoldingLowerMixedMeasurable upperUnfoldingLowerMixedSubgroupBorel upperUnfoldingLowerMixedSubgroupMeasurable upperUnfoldingMeasurable upperUnfoldingMixedMeasurable upperUnfoldingMixedSubgroupBorel upperUnfoldingMixedSubgroupMeasurable upperUnfoldingNBorel upperUnfoldingNCountable upperUnfoldingNMeasurable upperUnfoldingNQMeasurable upperUnfoldingT2 upperUnfoldingTopology upperUnfoldingValuation
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

local instance upperUnfoldingT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance upperUnfoldingCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance upperUnfoldingGLTopology (a : ℕ) : IsTopologicalGroup (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup a
local instance upperUnfoldingGLCountable (a : ℕ) : SecondCountableTopology (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology a
local instance upperUnfoldingMeasurable : MeasurableSpace F := borel _
local instance upperUnfoldingBorel : BorelSpace F := ⟨rfl⟩
local instance upperUnfoldingGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F) := borel _
local instance upperUnfoldingGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F) := ⟨rfl⟩
local instance upperUnfoldingNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F) := borel _
local instance upperUnfoldingNBorel (a : ℕ) : BorelSpace (upperUnipotent a F) := ⟨rfl⟩
local instance upperUnfoldingNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance upperUnfoldingNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F) := borel _
local instance upperUnfoldingNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable {ψ : UnitaryAdditiveCharacter F}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F)

local instance upperUnfoldingHQMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) := borel _
local instance upperUnfoldingHQBorel :
    BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F) := ⟨rfl⟩
local instance upperUnfoldingHMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h F) := borel _
local instance upperUnfoldingHBorel :
    BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h F) := ⟨rfl⟩
local instance upperUnfoldingMixedSubgroupMeasurable :
    MeasurableSpace (mixedSubgroup F h) := borel _
local instance upperUnfoldingMixedSubgroupBorel : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance upperUnfoldingLowerMixedSubgroupMeasurable :
    MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance upperUnfoldingLowerMixedSubgroupBorel : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance upperUnfoldingMixedMeasurable :
    MeasurableSpace (MixedQuotient F h) := borel _
local instance upperUnfoldingMixedBorel : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance upperUnfoldingLowerMixedMeasurable :
    MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance upperUnfoldingLowerMixedBorel : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

/-- A representative-independent upper first-block average on the actual lower
mixed quotient, obtained by the two actual quotient averages. -/
def firstBlockUpperQuotientAverage
    (νA : Measure (LeftUnipotentQuotient (m 0) F))
    (hInv : NormOneRightInvariant F (m 0) νA) (d : ℤ) :
    LowerMixedQuotient F h → ℂ :=
  radicalAverage F h (rectangularMeasure ν (m 1 + 1) (m 0 + 1))
    (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv d
      (rectangularSectionAverage F ell f j k Wtest ν
        (quotientDeterminantWeight F t (0 - ((j + k + 1 : ℕ) : ℂ) / 2))))

/-- The quotient average is measurable and integrable. The original raw norm
gives genuine triple-product convergence almost everywhere, where this average
equals the actual remaining-column integral of the upper coefficient. -/
theorem firstBlockUpperQuotientAverage_analysis
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (hσ : IsSmooth (σ 0))
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wmodel : (coefficientModel π lambda).toSubmodule)
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    [μR.IsAddHaarMeasure] (hraw : IsAbsIntegrable ψ (fun i => (ell i).val) μR f)
    (νN : Measure (LeftUnipotentQuotient t F))
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F)) [SigmaFinite νH]
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SigmaFinite νA]
    (νM : Measure (MixedQuotient F h)) (νL : Measure (LowerMixedQuotient F h))
    (hνN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) νN)
    (hνH : IsCompatible (TwoBlockUnipotentQuotient.blockUnipotent h F)
      (generalLinearHaar F t) (TwoBlockUnipotentQuotient.blockHaar F h) νH)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)
    (hνM : IsCompatible (mixedSubgroup F h) (generalLinearHaar F t)
      (mixedHaar F h) νM)
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F t)
      (lowerMixedHaar F h) νL) (d : ℤ) :
    let hInv := normOneRightInvariant_of_isCompatible F (m 0)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA hνA
    let Q := firstBlockUpperQuotientAverage F h j k ell f Wmodel.val ν νA hInv d
    let μZ := rectangularMeasure ν (m 1 + 1) (m 0 + 1)
    let μA := νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d)
    let μL := νL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)
    Measurable Q ∧ Integrable Q μL ∧
    (∀ᵐ qbase ∂μL, ∀ g : GeneralLinear (t + 1) F, qbase = Quotient.mk _ g →
      Integrable (fun z :
          (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F ×
            LeftUnipotentQuotient (m 0) F) ×
              Matrix (Fin j) (Fin (m 1 + 1)) F =>
        firstBlockUpperRowAverage F h j k ell f Wmodel.val ν 0 z.1.2 z.1.1 z.2 g)
        ((μZ.prod μA).prod (rectangularMeasure ν j (m 1 + 1))) ∧
      Q qbase = firstBlockUpperGlobalAverage F h j k ell f Wmodel.val ν νA d g) ∧
    (∫ q, Q q ∂μL) =
      (μZ {Z | ∀ i l, Z i l ∈ Valuation.integer
        (ValuativeRel.valuation F)}).toReal •
      ∫ z, rectangularSectionAverage F ell f j k Wmodel.val ν
        (quotientDeterminantWeight F t (0 - ((j + k + 1 : ℕ) : ℂ) / 2)) z
        ∂νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h d) := by
  dsimp only
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  let hInv := normOneRightInvariant_of_isCompatible F (m 0)
    (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA hνA
  let weight := quotientDeterminantWeight F t (0 - ((j + k + 1 : ℕ) : ℂ) / 2)
  let E := rectangularSectionAverage F ell f j k Wmodel.val ν weight
  let B := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv d E
  let μZ := rectangularMeasure ν (m 1 + 1) (m 0 + 1)
  let μA := νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d)
  let μL := νL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)
  have hw : Continuous weight := quotientDeterminantWeight_continuous F t _
  have hreg := rectangularSectionIntegrand_regular F ell f j k π hπ lambda Wmodel ν weight hw
  have hfirst := rectangularSectionAverage_firstBlock_unfolding F ell f j k π hπ lambda
    Wmodel weight hw μR hraw ν νN νH νA νM hνN hνH hνA hνM d
  have hBm : Measurable B := hfirst.1
  have hBi : Integrable B
      (νM.restrict (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantSlice F h 0)) := hfirst.2.1
  have hQm : Measurable (radicalAverage F h μZ B) := by
    rw [radicalAverage_eq_integral_radicalKernel F h μZ B hBm]
    exact (hBm.stronglyMeasurable.integral_kernel
      (κ := radicalKernel F h μZ)).measurable
  obtain ⟨κR, hκR, _, _, _, hBo⟩ := radicalIntegration F h μZ νL hνL νM hνM
  obtain ⟨_, hQi, hQeq⟩ := (hBo B hBm).2 hBi
  have hnorm := rectangularSection_firstBlock_product_fibers F ell f j k π hπ lambda
    Wmodel weight hw μR hraw ν νN νH νA νM hνN hνH hνA hνM d
  have hNae := integrable_firstBlock_radical_product_ae F h
    (rectangularSectionNormProfile F ell f j k Wmodel.val ν weight) hnorm.1
    μZ νH νA νM νL hνH hνA hνM hνL d hnorm.2.1
  refine ⟨hQm, hQi, ?_, ?_⟩
  · filter_upwards [hNae] with qbase hq g hqg
    have hrect : ∀ᵐ z ∂μZ.prod μA, Integrable (fun x =>
        rectangularSectionIntegrand F ell f j k Wmodel.val weight x
          (fiberPoint h F z.2 (lowerRadical h F z.1 * g)))
          (rectangularMeasure ν j (t + 1)) :=
      Filter.Eventually.of_forall fun _ => hreg.2.1 _
    obtain ⟨hprod, he⟩ := firstBlockUpperRowAverage_joint_product_control F h j k ell f
      Wmodel.val ν (glModelFunction_continuous ψ _ π hπ.1.1 lambda Wmodel) hσ 0
      μZ μA g hrect (hq g hqg)
    refine ⟨hprod, ?_⟩
    subst qbase
    change radicalAverage F h μZ B (Quotient.mk _ g) = _
    rw [radicalAverage_mk]
    simp only [B, radicalFiberPoint_def, Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage_mk]
    exact he
  · exact hQeq.trans (congrArg (fun z : ℂ =>
      (μZ {Z | ∀ i l, Z i l ∈ Valuation.integer
        (ValuativeRel.valuation F)}).toReal • z) hfirst.2.2.symm)

/-- Transposing the dimensions preserves the integral-cube mass of the
supplied scalar product Haar measure. -/
theorem rectangular_integerCube_mass_swap (a b : ℕ) :
    (rectangularMeasure ν a b)
      {Z | ∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F)} =
    (rectangularMeasure ν b a)
      {Z | ∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F)} := by
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  change
    (Measure.pi (fun _ : Fin a => Measure.pi (fun _ : Fin b => ν.measure)))
      {Z : Fin a → Fin b → F |
        ∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F)} =
    (Measure.pi (fun _ : Fin b => Measure.pi (fun _ : Fin a => ν.measure)))
      {Z : Fin b → Fin a → F |
        ∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F)}
  have hc (a b : ℕ) :
      {Z : Fin a → Fin b → F |
        ∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F)} =
      Set.univ.pi (fun _ : Fin a => Set.univ.pi (fun _ : Fin b =>
        (Valuation.integer (ValuativeRel.valuation F) : Set F))) := by
    ext Z
    change (∀ i l, Z i l ∈ Valuation.integer (ValuativeRel.valuation F)) ↔
      (∀ i ∈ Set.univ, ∀ l ∈ Set.univ,
        Z i l ∈ Valuation.integer (ValuativeRel.valuation F))
    simp
  simp only [hc, Measure.pi_pi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [Nat.mul_comm]

/-- With the actual Jacquet realization and the supplied scalar product
measure, the upper quotient integral is exactly the original large JPSS
coefficient. The two integral-cube constants agree, so no rescaling remains. -/
theorem firstBlockUpperQuotientAverage_integral_eq_large
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (hσ : IsSmooth (σ 0))
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wmodel : (coefficientModel π lambda).toSubmodule)
    (Wjac : InverseWhittakerFunctions ψ t)
    (hjac : ∀ g : GeneralLinear (t + 1) F,
      Wjac.val g = jacquetFunction ψ (fun i => (ell i).val)
        (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) f g)
    (hraw : IsAbsIntegrable ψ (fun i => (ell i).val)
      (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) f)
    (νN : Measure (LeftUnipotentQuotient t F)) [SigmaFinite νN]
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F)) [SigmaFinite νH]
    (νA : Measure (LeftUnipotentQuotient (m 0) F)) [SigmaFinite νA]
    (νM : Measure (MixedQuotient F h)) (νL : Measure (LowerMixedQuotient F h))
    (hνN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) νN)
    (hνH : IsCompatible (TwoBlockUnipotentQuotient.blockUnipotent h F)
      (generalLinearHaar F t) (TwoBlockUnipotentQuotient.blockHaar F h) νH)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA)
    (hνM : IsCompatible (mixedSubgroup F h) (generalLinearHaar F t)
      (mixedHaar F h) νM)
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F t)
      (lowerMixedHaar F h) νL) (d : ℤ) :
    let hInv := normOneRightInvariant_of_isCompatible F (m 0)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA hνA
    (∫ q, firstBlockUpperQuotientAverage F h j k ell f Wmodel.val ν νA hInv d q
      ∂νL.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)) =
    ∫ q, ∫ X, unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      j k Wmodel.val Wjac 0 X q ∂rectangularMeasure ν j (t + 1)
        ∂νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t d) := by
  dsimp only
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hu := firstBlockUpperQuotientAverage_analysis F h j k ell f ν π hπ hσ lambda Wmodel
    (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) hraw
    νN νH νA νM νL hνN hνH hνA hνM hνL d
  have hl := rectangularSection_slice_unfolding F ell f
    (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) Wjac hjac
    j k π hπ lambda Wmodel hraw ν νN νH hνN hνH d 0
  rw [hu.2.2.2]
  rw [rectangular_integerCube_mass_swap F ν (m 1 + 1) (m 0 + 1)]
  exact hl.2.2.symm

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
