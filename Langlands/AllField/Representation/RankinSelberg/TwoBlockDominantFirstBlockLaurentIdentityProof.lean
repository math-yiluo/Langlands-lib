import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantAnalyticInputs
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockGlobalLaurent
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement
/-! # The strict-dominant first-block JPSS Laurent identity -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockDominantFirstBlockLaurentIdentityStatement TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockDominantFirstBlockLaurentIdentity twoBlockFirstBlockQuotientIntegration twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement exists_rowSchwartz_order_lower_bound measurePreserving_rectangular_mul_mul padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding HasUniformAnalyticInputs UpperSliceConverges analyticInputsGLBorel analyticInputsGLGroup analyticInputsGLMeasurable analyticInputsLocalField analyticInputsLowerBorel analyticInputsLowerMeasurable analyticInputsNBorel analyticInputsNMeasurable analyticInputsQBorel analyticInputsQMeasurable analyticInputsT2 analyticInputsTopology analyticInputsValuation compatible_standard_quotients continuous_diagonalIntegrand continuous_firstBlockDualFiberIntegrand_reflection continuous_translated_unequalRankIntegrandAt continuous_upperAverage determinantWeight_firstBlockEmbedding determinantWeight_lowerRadical diagonalSupportGLTopological diagonalSupportT2 diagonalSupportTopology diagonalWhittaker_slice_hasCompactSupport disintegrationGLBorel disintegrationGLMeasurable disintegrationLocalField disintegrationMeasurable disintegrationQuotientMeasurable disintegrationTopology disintegrationUpperBorel disintegrationUpperMeasurable disintegrationValuation exists_rectangularSectionExpansion exists_uniformOrdinaryJacquetRealization exists_uniform_analytic_inputs firstBlockDualFiberIntegral_reflection firstBlockDualFiberIntegral_reflection_on_slice firstBlockDualFiberIntegrand firstBlockDualFiberIntegrand_reflection firstBlockFiberIntegrand firstBlockReflectedColumnNormProfile firstBlockReflectedQuotientAverage firstBlockReflectedQuotientAverage_analysis firstBlockReflectedRowAverage firstBlockReflectedRowAverage_column_control firstBlockReflectedRowAverage_mk_on_slice firstBlockReflectedRowAverage_product_control firstBlockReflectedRowAverage_stronglyMeasurable firstBlockReflectedSmallCoefficient firstBlockReflectedSmallCoefficient_eq_sliceIntegral firstBlockReflectionDensity firstBlockReflectionDensity_nonneg firstBlockRowJacobian firstBlockUpperCoefficient firstBlockUpperCoefficient_eq_small firstBlockUpperCoefficient_eq_small_of_whittakerType firstBlockUpperCoefficient_integrable_of_product firstBlockUpperColumnNormProfile firstBlockUpperGlobalAverage firstBlockUpperQuotientAverage firstBlockUpperQuotientAverage_analysis firstBlockUpperQuotientAverage_integral_eq_large firstBlockUpperRowAverage firstBlockUpperRowAverage_column_control firstBlockUpperRowAverage_eq firstBlockUpperRowAverage_joint_product_control firstBlockUpperRowAverage_joint_stronglyMeasurable firstBlockUpperValue firstBlockUpperValue_eq_rowScaled firstBlockUpperValue_fiber firstBlock_global_laurent_identity firstBlock_small_laurent_identity firstCoordinatesBorel firstCoordinatesLocalField firstCoordinatesMatrixBorel firstCoordinatesMeasurable firstCoordinatesSecondCountable firstCoordinatesTopology firstCoordinatesValuation firstFiberBorel firstFiberCountable firstFiberGLBorel firstFiberGLCountable firstFiberGLMeasurable firstFiberGLTopology firstFiberHBorel firstFiberHMeasurable firstFiberHQBorel firstFiberHQMeasurable firstFiberLocalField firstFiberMeasurable firstFiberMixedMeasurable firstFiberMixedSubgroupBorel firstFiberMixedSubgroupMeasurable firstFiberNBorel firstFiberNCountable firstFiberNMeasurable firstFiberNQBorel firstFiberNQMeasurable firstFiberT2 firstFiberTopology firstFiberValuation firstQuotientCountable firstQuotientGLBorel firstQuotientGLCountable firstQuotientGLMeasurable firstQuotientGLTopology firstQuotientHBorel firstQuotientHMeasurable firstQuotientHQBorel firstQuotientHQMeasurable firstQuotientLocalField firstQuotientMeasurable firstQuotientMixedMeasurable firstQuotientMixedSubgroupBorel firstQuotientMixedSubgroupMeasurable firstQuotientNBorel firstQuotientNCountable firstQuotientNMeasurable firstQuotientNQMeasurable firstQuotientT2 firstQuotientTopology firstQuotientValuation globalAnalysisBorel globalAnalysisCountable globalAnalysisGLBorel globalAnalysisGLCountable globalAnalysisGLMeasurable globalAnalysisGLTopology globalAnalysisHBorel globalAnalysisHMeasurable globalAnalysisHQBorel globalAnalysisHQMeasurable globalAnalysisLocalField globalAnalysisLowerMixedMeasurable globalAnalysisLowerMixedSubgroupBorel globalAnalysisLowerMixedSubgroupMeasurable globalAnalysisMeasurable globalAnalysisMixedBorel globalAnalysisMixedMeasurable globalAnalysisMixedSubgroupBorel globalAnalysisMixedSubgroupMeasurable globalAnalysisNBorel globalAnalysisNCountable globalAnalysisNMeasurable globalAnalysisNQBorel globalAnalysisNQMeasurable globalAnalysisT2 globalAnalysisTopology globalAnalysisValuation globalLaurentBorel globalLaurentCountable globalLaurentGLBorel globalLaurentGLCountable globalLaurentGLMeasurable globalLaurentGLTopology globalLaurentHBorel globalLaurentHMeasurable globalLaurentHQMeasurable globalLaurentLocalField globalLaurentLowerHBorel globalLaurentLowerHMeasurable globalLaurentLowerMeasurable globalLaurentLowerMixedMeasurable globalLaurentLowerMixedSubgroupBorel globalLaurentLowerMixedSubgroupMeasurable globalLaurentMeasurable globalLaurentMixedMeasurable globalLaurentMixedSubgroupBorel globalLaurentMixedSubgroupMeasurable globalLaurentNBorel globalLaurentNCountable globalLaurentNMeasurable globalLaurentNQMeasurable globalLaurentT2 globalLaurentTopology globalLaurentValuation instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_firstBlockRowChange_iff integrable_firstBlockUpperValue_original_iff integrable_firstBlock_radical_product_ae integrable_rectangularBorelMeasure integral_firstBlockReflectedRectangle integral_firstBlockRowChange integral_firstBlockUpperValue integral_firstBlockUpperValue_columns integral_firstBlockUpperValue_original integral_norm_firstBlockUpperValue_columns integral_norm_firstBlockUpperValue_original integrandBridgeMeasurable integrandBridgeTopology quotientDeterminantWeight quotientDeterminantWeight_continuous quotientDeterminantWeight_mk radicalUnfoldingBorel radicalUnfoldingCountable radicalUnfoldingGLBorel radicalUnfoldingGLCountable radicalUnfoldingGLMeasurable radicalUnfoldingGLTopology radicalUnfoldingHBorel radicalUnfoldingHMeasurable radicalUnfoldingHQMeasurable radicalUnfoldingLocalField radicalUnfoldingMeasurable radicalUnfoldingNBorel radicalUnfoldingNCountable radicalUnfoldingNMeasurable radicalUnfoldingNQMeasurable radicalUnfoldingT2 radicalUnfoldingTopology radicalUnfoldingValuation rectangleChangeMeasurable rectangleChangeTopology rectangleUnfoldingCountable rectangleUnfoldingGLBorel rectangleUnfoldingGLCountable rectangleUnfoldingGLMeasurable rectangleUnfoldingGLTopology rectangleUnfoldingHBorel rectangleUnfoldingHMeasurable rectangleUnfoldingHQMeasurable rectangleUnfoldingLocalField rectangleUnfoldingMeasurable rectangleUnfoldingNBorel rectangleUnfoldingNCountable rectangleUnfoldingNMeasurable rectangleUnfoldingNQMeasurable rectangleUnfoldingT2 rectangleUnfoldingTopology rectangleUnfoldingValuation rectangularBorelMeasure rectangularMeasure_map_firstBlockReflectedRectangle rectangularMeasure_map_firstBlockRowChange rectangularSectionAverage rectangularSectionAverage_firstBlock_unfolding rectangularSectionIntegrand rectangularSectionIntegrand_expansion rectangularSectionIntegrand_integrable rectangularSectionIntegrand_mk rectangularSectionIntegrand_regular rectangularSectionNormProfile rectangularSection_firstBlock_product_fibers rectangularSection_slice_unfolding rectangularWhittaker rectangularWhittaker_apply rectangular_integerCube_mass_swap reflectionAverageBorel reflectionAverageCountable reflectionAverageGLBorel reflectionAverageGLMeasurable reflectionAverageGLTopology reflectionAverageLocalField reflectionAverageMatrixBorel reflectionAverageMatrixCountable reflectionAverageMeasurable reflectionAverageNBorel reflectionAverageNMeasurable reflectionAverageNQBorel reflectionAverageNQMeasurable reflectionAverageTopology reflectionAverageValuation reflectionCoefficientGLBorel reflectionCoefficientGLMeasurable reflectionCoefficientGLTopology reflectionCoefficientLocalField reflectionCoefficientMeasurable reflectionCoefficientNBorel reflectionCoefficientNMeasurable reflectionCoefficientNQMeasurable reflectionCoefficientTopology reflectionCoefficientValuation reflectionGlobalGLBorel reflectionGlobalGLMeasurable reflectionGlobalGLTopology reflectionGlobalLocalField reflectionGlobalLowerBorel reflectionGlobalLowerHBorel reflectionGlobalLowerHMeasurable reflectionGlobalLowerMeasurable reflectionGlobalLowerMixedMeasurable reflectionGlobalLowerMixedSubgroupBorel reflectionGlobalLowerMixedSubgroupMeasurable reflectionGlobalMeasurable reflectionGlobalNBorel reflectionGlobalNMeasurable reflectionGlobalNQBorel reflectionGlobalNQMeasurable reflectionGlobalTopology reflectionGlobalValuation reflectionIntegrandLocalField reflectionIntegrandTopology reflectionIntegrandValuation reflectionMeasureBorel reflectionMeasureCountable reflectionMeasureLocalField reflectionMeasureMatrixBorel reflectionMeasureMeasurable reflectionMeasureT2 reflectionMeasureTopology reflectionMeasureValuation rowAnalysisGLTopology rowAnalysisLocalField rowAnalysisMeasurable rowAnalysisTopology rowAnalysisValuation sectionAverage_mk sectionAverages_continuous sectionIntegrand sectionIntegrand_continuous sectionIntegrand_fiberPoint sectionIntegrand_mk sectionIntegrand_slice_unfolding sectionNormAverage_mk sectionUnfoldingBorel sectionUnfoldingCountable sectionUnfoldingGLBorel sectionUnfoldingGLCountable sectionUnfoldingGLLocalCompact sectionUnfoldingGLMeasurable sectionUnfoldingGLTopology sectionUnfoldingHBorel sectionUnfoldingHMeasurable sectionUnfoldingHQBorel sectionUnfoldingHQMeasurable sectionUnfoldingLocalField sectionUnfoldingMeasurable sectionUnfoldingNBorel sectionUnfoldingNCountable sectionUnfoldingNMeasurable sectionUnfoldingNQBorel sectionUnfoldingNQMeasurable sectionUnfoldingT2 sectionUnfoldingTopology sectionUnfoldingValuation smallLaurentGLBorel smallLaurentGLMeasurable smallLaurentGLTopology smallLaurentLocalField smallLaurentMeasurable smallLaurentNBorel smallLaurentNMeasurable smallLaurentNQMeasurable smallLaurentTopology smallLaurentValuation unequalRankIntegrandAt_mk unequalRankMatrix_rectangle_change unequalRankSliceCoefficientAt_eq_integral upperSliceConverges upperSliceConvergesAt upperUnfoldingBorel upperUnfoldingCountable upperUnfoldingGLBorel upperUnfoldingGLCountable upperUnfoldingGLMeasurable upperUnfoldingGLTopology upperUnfoldingHBorel upperUnfoldingHMeasurable upperUnfoldingHQMeasurable upperUnfoldingLocalField upperUnfoldingLowerMixedMeasurable upperUnfoldingLowerMixedSubgroupBorel upperUnfoldingLowerMixedSubgroupMeasurable upperUnfoldingMeasurable upperUnfoldingMixedMeasurable upperUnfoldingMixedSubgroupBorel upperUnfoldingMixedSubgroupMeasurable upperUnfoldingNBorel upperUnfoldingNCountable upperUnfoldingNMeasurable upperUnfoldingNQMeasurable upperUnfoldingT2 upperUnfoldingTopology upperUnfoldingValuation
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock

universe uF uV uW

private theorem integral_measurableSpace_transport {X : Type*}
    {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂)
    (μ : @Measure X m₁) (φ : X → ℂ) :
    (letI := m₂; ∫ x, φ x ∂(hm ▸ μ)) =
      (letI := m₁; ∫ x, φ x ∂μ) := by
  cases hm
  rfl

/-- The exact closed dominant first-block identity, with the ordinary Jacquet
functional and actual convergence fixed before all measures and tests. -/
theorem twoBlockDominantFirstBlockLaurentIdentity :
    TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW} := by
  intro F _ _ _ _ T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ ν t r m h htr hlt
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  intro G N GA NA NQ AQ LQ
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace GA := borel GA
  let : BorelSpace GA := ⟨rfl⟩
  let : MeasurableSpace NA := borel NA
  let : BorelSpace NA := ⟨rfl⟩
  let : MeasurableSpace NQ := borel NQ
  let : BorelSpace NQ := ⟨rfl⟩
  let : MeasurableSpace AQ := borel AQ
  let : BorelSpace AQ := ⟨rfl⟩
  let : MeasurableSpace LQ := borel LQ
  let : BorelSpace LQ := ⟨rfl⟩
  intro μG μN μGA μNA μR q abv
  refine ⟨compatible_standard_quotients F t (m 0), ?_⟩
  intro V _ _ π hπ lambda W _ _ τ hτ ell
  obtain ⟨C, hC⟩ := exists_uniform_analytic_inputs F h ψ ν π hπ lambda τ hτ ell
  refine ⟨C, ?_⟩
  intro u hu σu ellu
  obtain ⟨habs, J, hJ0, hJ, hmeasures⟩ := hC u hu
  refine ⟨habs, J, hJ0, hJ, ?_⟩
  intro hN hNA
  let := hN
  let := hNA
  intro νN νA hνN hνA νMinus
  obtain ⟨hsfN, hsfA, hsfMinus, hconv⟩ := hmeasures hN hNA νN νA hνN hνA
  let := hsfN
  let := hsfA
  let := hsfMinus
  refine ⟨hsfN, hsfA, hsfMinus, hconv, ?_⟩
  intro cε d hε
  obtain ⟨ζ, P, Pdual, hζ, hbody⟩ := hε
  refine ⟨ζ, P, Pdual, hζ, hbody, ?_⟩
  intro j k hr f Wtest
  subst r
  dsimp only
  obtain ⟨hP, hPd, hpairs⟩ := hbody (m 1 + 1 + j) k (firstBlockSmallRank h j k)
  have hσ : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σu 0) :=
    (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u 0
      (inverseStandardCharacter ψ (m 0))).mpr
      ((isOfWhittakerType_standard_iff_inverse ψ (τ 0)).mp (hτ 0))
  let : ∀ n, IsTopologicalGroup (GeneralLinear n F) :=
    T.generalLinearTopologicalGroup
  let : ∀ n, LocallyCompactSpace (GeneralLinear n F) :=
    T.generalLinearLocallyCompactSpace
  let : ∀ n, SecondCountableTopology (GeneralLinear n F) :=
    T.generalLinearSecondCountableTopology
  let : ∀ n, MeasurableSpace (GeneralLinear n F) := fun _ => borel _
  let : ∀ n, BorelSpace (GeneralLinear n F) := fun _ => ⟨rfl⟩
  let : ∀ n, MeasurableSpace (upperUnipotent n F) := fun _ => borel _
  let : ∀ n, BorelSpace (upperUnipotent n F) := fun _ => ⟨rfl⟩
  let : ∀ n, SecondCountableTopology (upperUnipotent n F) :=
    fun _ => Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let HQ := TwoBlockUnipotentQuotient.BlockQuotient h F
  let H := TwoBlockUnipotentQuotient.blockUnipotent h F
  let MQ := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.MixedQuotient F h
  let LMQ := Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.LowerMixedQuotient F h
  let MS := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroup F h
  let LMS := Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixedSubgroup F h
  let LH := TwoBlockLowerUnipotentQuotient.lowerBlockUnipotent h F
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace MQ := borel MQ
  let : BorelSpace MQ := ⟨rfl⟩
  let : MeasurableSpace LMQ := borel LMQ
  let : BorelSpace LMQ := ⟨rfl⟩
  let : MeasurableSpace MS := borel MS
  let : BorelSpace MS := ⟨rfl⟩
  let : MeasurableSpace LMS := borel LMS
  let : BorelSpace LMS := ⟨rfl⟩
  let : MeasurableSpace LH := borel LH
  let : BorelSpace LH := ⟨rfl⟩
  obtain ⟨νH, hνH⟩ := TwoBlockUnipotentQuotient.block_compatibleMeasureExists F h
  obtain ⟨νM, hνM⟩ := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixed_compatibleMeasureExists F h
  obtain ⟨νL, hνL⟩ := Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMixed_compatibleMeasureExists F h
  have hsfH := Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.compatibleQuotient_sigmaFinite F t H
    (TwoBlockUnipotentQuotient.isClosed_blockUnipotent h F)
    (TwoBlockUnipotentQuotient.blockHaar F h) νH hνH
  let := hsfH
  have hνMinus := Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.lowerMeasure_isCompatible F h νN hνN
  have hi := firstBlock_global_laurent_identity F h j k ellu f ν.val π hπ hσ.1.1
    lambda Wtest (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu) J f).val
    (fun g => hJ f g) (habs f) νN νH νA νM νL νMinus
    hνN hνH hνA hνM hνL hνMinus
    (fun a => (hconv j k rfl f Wtest).2.2 a |>.2)
    (TwoBlockFirstBlockLaurent.reflectedPolynomial q Pdual)
    (LaurentPolynomial.C ((ζ : ℂ) ^ (t + (j + k + 1)) * (cε : ℂ)) *
      LaurentPolynomial.T d * P.toLaurent)
    (fun Y g => firstBlock_small_laurent_identity F h j k ellu f ν.val π lambda
      hπ hσ Wtest νA hνA ζ cε d P Pdual hP hPd hpairs Y g)
  have hupper :
      Langlands.AllField.RankinSelberg.unequalRankSliceCoefficient F j k ψ νN
        (rectangularBorelMeasure F ν.val j (t + 1)) Wtest.val
        (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu) J f).val =
      (fun a => ∫ z, ∫ X, unequalRankIntegrand ψ abv j k Wtest.val
        (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu) J f).val 0 X z
          ∂rectangularMeasure ν.val j (t + 1)
          ∂νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice T t a)) := by
    funext a
    change (∫ z, ∫ X, unequalRankIntegrand ψ abv j k Wtest.val
      (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu) J f).val 0 X z
        ∂rectangularBorelMeasure F ν.val j (t + 1)
        ∂νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice T t a)) = _
    apply integral_congr_ae
    filter_upwards [] with z
    exact integral_measurableSpace_transport _ _ _
  erw [hupper]
  exact hi

end Langlands.AllField.RankinSelberg
