import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockRectangleChange
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockDisintegration
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockFibers
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRadicalUnfolding
/-! # Original external rectangle change and exact column measures -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding UpperSliceConverges continuous_diagonalIntegrand continuous_upperAverage determinantWeight_firstBlockEmbedding determinantWeight_lowerRadical diagonalSupportGLTopological diagonalSupportT2 diagonalSupportTopology diagonalWhittaker_slice_hasCompactSupport disintegrationGLBorel disintegrationGLMeasurable disintegrationLocalField disintegrationMeasurable disintegrationQuotientMeasurable disintegrationTopology disintegrationUpperBorel disintegrationUpperMeasurable disintegrationValuation exists_rectangularSectionExpansion exists_uniformOrdinaryJacquetRealization firstBlockFiberIntegrand firstBlockRowJacobian firstBlockUpperCoefficient firstBlockUpperCoefficient_eq_small firstBlockUpperCoefficient_eq_small_of_whittakerType firstBlockUpperRowAverage firstBlockUpperRowAverage_eq firstBlockUpperValue firstBlockUpperValue_eq_rowScaled firstBlockUpperValue_fiber firstCoordinatesBorel firstCoordinatesLocalField firstCoordinatesMatrixBorel firstCoordinatesMeasurable firstCoordinatesSecondCountable firstCoordinatesTopology firstCoordinatesValuation firstFiberBorel firstFiberCountable firstFiberGLBorel firstFiberGLCountable firstFiberGLMeasurable firstFiberGLTopology firstFiberHBorel firstFiberHMeasurable firstFiberHQBorel firstFiberHQMeasurable firstFiberLocalField firstFiberMeasurable firstFiberMixedMeasurable firstFiberMixedSubgroupBorel firstFiberMixedSubgroupMeasurable firstFiberNBorel firstFiberNCountable firstFiberNMeasurable firstFiberNQBorel firstFiberNQMeasurable firstFiberT2 firstFiberTopology firstFiberValuation firstQuotientCountable firstQuotientGLBorel firstQuotientGLCountable firstQuotientGLMeasurable firstQuotientGLTopology firstQuotientHBorel firstQuotientHMeasurable firstQuotientHQBorel firstQuotientHQMeasurable firstQuotientLocalField firstQuotientMeasurable firstQuotientMixedMeasurable firstQuotientMixedSubgroupBorel firstQuotientMixedSubgroupMeasurable firstQuotientNBorel firstQuotientNCountable firstQuotientNMeasurable firstQuotientNQMeasurable firstQuotientT2 firstQuotientTopology firstQuotientValuation instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_firstBlockRowChange_iff integrable_firstBlockUpperValue_original_iff integrable_rectangularBorelMeasure integral_firstBlockRowChange integral_firstBlockUpperValue integral_firstBlockUpperValue_columns integral_firstBlockUpperValue_original integral_norm_firstBlockUpperValue_columns integral_norm_firstBlockUpperValue_original integrandBridgeMeasurable integrandBridgeTopology quotientDeterminantWeight quotientDeterminantWeight_continuous quotientDeterminantWeight_mk radicalUnfoldingBorel radicalUnfoldingCountable radicalUnfoldingGLBorel radicalUnfoldingGLCountable radicalUnfoldingGLMeasurable radicalUnfoldingGLTopology radicalUnfoldingHBorel radicalUnfoldingHMeasurable radicalUnfoldingHQMeasurable radicalUnfoldingLocalField radicalUnfoldingMeasurable radicalUnfoldingNBorel radicalUnfoldingNCountable radicalUnfoldingNMeasurable radicalUnfoldingNQMeasurable radicalUnfoldingT2 radicalUnfoldingTopology radicalUnfoldingValuation rectangleChangeMeasurable rectangleChangeTopology rectangleUnfoldingCountable rectangleUnfoldingGLBorel rectangleUnfoldingGLCountable rectangleUnfoldingGLMeasurable rectangleUnfoldingGLTopology rectangleUnfoldingHBorel rectangleUnfoldingHMeasurable rectangleUnfoldingHQMeasurable rectangleUnfoldingLocalField rectangleUnfoldingMeasurable rectangleUnfoldingNBorel rectangleUnfoldingNCountable rectangleUnfoldingNMeasurable rectangleUnfoldingNQMeasurable rectangleUnfoldingT2 rectangleUnfoldingTopology rectangleUnfoldingValuation rectangularBorelMeasure rectangularMeasure_map_firstBlockRowChange rectangularSectionAverage rectangularSectionAverage_firstBlock_unfolding rectangularSectionIntegrand rectangularSectionIntegrand_expansion rectangularSectionIntegrand_integrable rectangularSectionIntegrand_mk rectangularSectionIntegrand_regular rectangularSectionNormProfile rectangularSection_firstBlock_product_fibers rectangularSection_slice_unfolding rectangularWhittaker rectangularWhittaker_apply sectionAverage_mk sectionAverages_continuous sectionIntegrand sectionIntegrand_continuous sectionIntegrand_fiberPoint sectionIntegrand_mk sectionIntegrand_slice_unfolding sectionNormAverage_mk sectionUnfoldingBorel sectionUnfoldingCountable sectionUnfoldingGLBorel sectionUnfoldingGLCountable sectionUnfoldingGLLocalCompact sectionUnfoldingGLMeasurable sectionUnfoldingGLTopology sectionUnfoldingHBorel sectionUnfoldingHMeasurable sectionUnfoldingHQBorel sectionUnfoldingHQMeasurable sectionUnfoldingLocalField sectionUnfoldingMeasurable sectionUnfoldingNBorel sectionUnfoldingNCountable sectionUnfoldingNMeasurable sectionUnfoldingNQBorel sectionUnfoldingNQMeasurable sectionUnfoldingT2 sectionUnfoldingTopology sectionUnfoldingValuation unequalRankIntegrandAt_mk unequalRankMatrix_rectangle_change unequalRankSliceCoefficientAt_eq_integral upperSliceConverges upperSliceConvergesAt
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockFirstBlockQuotientIntegration twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
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
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk iUnion_determinantSlice integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurePreserving_radicalChange mem_determinantSlice mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice pairwise_disjoint_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped NNReal

universe uF uW uE

section Columns



end Columns

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance rectangleChangeCountable : SecondCountableTopology F := (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance rectangleChangeMeasurable : MeasurableSpace F := borel _
local instance rectangleChangeBorel : BorelSpace F := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable {ψ : UnitaryAdditiveCharacter F}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))

/-- Moving the external rectangle to the left is exactly `x = X*g`. -/
theorem unequalRankMatrix_rectangle_change
    (g : GeneralLinear (t + 1) F)
    (X : Matrix (Fin j) (Fin (t + 1)) F) :
    unequalRankMatrix j k g (X * g.val) =
      rectangularUnipotent j k X * appendIdentity t (j + k + 1) g := by
  simpa only [unequalRankMatrix, map_one, one_mul] using
    (unequalRankMatrix_mul_appendIdentity j k (1 : GeneralLinear (t + 1) F) g X).symm

/-- The extra determinant power in the upper value is precisely the row scale. -/
theorem firstBlockUpperValue_eq_rowScaled (s : ℂ)
    (g : GeneralLinear (t + 1) F)
    (X : Matrix (Fin j) (Fin (t + 1)) F) :
    firstBlockUpperValue F h j k ell f Wtest s g X =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g (j : ℂ) *
        rectangularSectionIntegrand F ell f j k Wtest
          (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
          (X * g.val) (Quotient.mk _ g) := by
  rw [rectangularSectionIntegrand_mk, quotientDeterminantWeight_mk,
    unequalRankMatrix_rectangle_change, firstBlockUpperValue, determinantWeight_add]
  ring

/-- The original rectangle substitution cancels its exact Haar Jacobian. -/
theorem integral_firstBlockUpperValue_original (ν : AdditiveHaarMeasure F)
    (s : ℂ) (g : GeneralLinear (t + 1) F) :
    (∫ X, firstBlockUpperValue F h j k ell f Wtest s g X
      ∂rectangularMeasure ν j (t + 1)) =
      rectangularSectionAverage F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (Quotient.mk _ g) := by
  simp_rw [firstBlockUpperValue_eq_rowScaled]
  rw [integral_const_mul]
  have hchange := integral_firstBlockRowChange F ν g
    (0 : Matrix (Fin 0) (Fin (t + 1)) F)
    (0 : Matrix (Fin j) (Fin 0) F)
    (fun x => rectangularSectionIntegrand F ell f j k Wtest
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)) x (Quotient.mk _ g))
  simp only [Matrix.zero_mul, add_zero] at hchange
  rw [hchange, NNReal.smul_def, Complex.real_smul,
    firstBlockRowJacobian F (m := fun _ : Fin 2 => t) j g,
    ← mul_assoc, ← determinantWeight_add]
  simp [rectangularSectionAverage, determinantWeight]

/-- Absolute integrability is equivalent under the original rectangle change. -/
theorem integrable_firstBlockUpperValue_original_iff (ν : AdditiveHaarMeasure F)
    (s : ℂ) (g : GeneralLinear (t + 1) F) :
    Integrable (fun X => firstBlockUpperValue F h j k ell f Wtest s g X)
      (rectangularMeasure ν j (t + 1)) ↔
    Integrable (fun x => rectangularSectionIntegrand F ell f j k Wtest
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)) x (Quotient.mk _ g))
      (rectangularMeasure ν j (t + 1)) := by
  simp_rw [firstBlockUpperValue_eq_rowScaled]
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (determinantWeight_ne_zero _ _ _))]
  simpa only [Matrix.zero_mul, add_zero] using
    integrable_firstBlockRowChange_iff F ν g
      (0 : Matrix (Fin 0) (Fin (t + 1)) F)
      (0 : Matrix (Fin j) (Fin 0) F)
      (fun x => rectangularSectionIntegrand F ell f j k Wtest
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        x (Quotient.mk _ g))

/-- The real raw-norm integral has the same exact Jacobian cancellation. -/
theorem integral_norm_firstBlockUpperValue_original (ν : AdditiveHaarMeasure F)
    (s : ℂ) (g : GeneralLinear (t + 1) F) :
    (∫ X, ‖firstBlockUpperValue F h j k ell f Wtest s g X‖
      ∂rectangularMeasure ν j (t + 1)) =
      rectangularSectionNormProfile F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (Quotient.mk _ g) := by
  simp_rw [firstBlockUpperValue_eq_rowScaled, norm_mul]
  rw [integral_const_mul]
  have hchange := integral_firstBlockRowChange F ν g
    (0 : Matrix (Fin 0) (Fin (t + 1)) F)
    (0 : Matrix (Fin j) (Fin 0) F)
    (fun x => ‖rectangularSectionIntegrand F ell f j k Wtest
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
      x (Quotient.mk _ g)‖)
  simp only [Matrix.zero_mul, add_zero] at hchange
  rw [hchange, NNReal.smul_def, smul_eq_mul, ← mul_assoc]
  have hc :
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g (j : ℂ) *
        ((((((⟨⟩ : LocalFieldData F).determinantNorm (t + 1) g : ℝ≥0) ^ j)⁻¹ :
          ℝ≥0) : ℝ) : ℂ) = 1 := by
    rw [firstBlockRowJacobian F (m := fun _ : Fin 2 => t) j g,
      ← determinantWeight_add]
    simp [determinantWeight]
  have hr := congrArg norm hc
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (NNReal.coe_nonneg _), norm_one] at hr
  rw [hr, one_mul]
  rfl

/-- Once rectangle convergence is known, splitting the columns retains the
actual original rectangle average. -/
theorem integral_firstBlockUpperValue_columns (ν : AdditiveHaarMeasure F)
    (s : ℂ) (g : GeneralLinear (t + 1) F)
    (hi : Integrable (fun x => rectangularSectionIntegrand F ell f j k Wtest
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
      x (Quotient.mk _ g)) (rectangularMeasure ν j (t + 1))) :
    (∫ Y, ∫ U, firstBlockUpperValue F h j k ell f Wtest s g
      (firstBlockColumns h j U Y)
        ∂rectangularMeasure ν j (m 0 + 1) ∂rectangularMeasure ν j (m 1 + 1)) =
      rectangularSectionAverage F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (Quotient.mk _ g) := by
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hu := (integrable_firstBlockUpperValue_original_iff
    F h j k ell f Wtest ν s g).mpr hi
  exact (integral_firstBlockColumns F h j ν _ hu).symm.trans
    (integral_firstBlockUpperValue_original F h j k ell f Wtest ν s g)

/-- The column-split raw-norm integral is the original real norm profile. -/
theorem integral_norm_firstBlockUpperValue_columns (ν : AdditiveHaarMeasure F)
    (s : ℂ) (g : GeneralLinear (t + 1) F)
    (hi : Integrable (fun x => rectangularSectionIntegrand F ell f j k Wtest
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
      x (Quotient.mk _ g)) (rectangularMeasure ν j (t + 1))) :
    (∫ Y, ∫ U, ‖firstBlockUpperValue F h j k ell f Wtest s g
      (firstBlockColumns h j U Y)‖
        ∂rectangularMeasure ν j (m 0 + 1) ∂rectangularMeasure ν j (m 1 + 1)) =
      rectangularSectionNormProfile F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (Quotient.mk _ g) := by
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hu := (integrable_firstBlockUpperValue_original_iff
    F h j k ell f Wtest ν s g).mpr hi
  exact (integral_firstBlockColumns F h j ν _ hu.norm).symm.trans
    (integral_norm_firstBlockUpperValue_original F h j k ell f Wtest ν s g)

end Padic

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
