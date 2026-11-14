import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionAverages
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionCoefficients
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantKernelRegularity
/-! # Convergent reflected first-block averages -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding UpperSliceConverges continuous_diagonalIntegrand continuous_firstBlockDualFiberIntegrand_reflection continuous_upperAverage determinantWeight_firstBlockEmbedding determinantWeight_lowerRadical disintegrationGLBorel disintegrationGLMeasurable disintegrationLocalField disintegrationMeasurable disintegrationQuotientMeasurable disintegrationTopology disintegrationUpperBorel disintegrationUpperMeasurable disintegrationValuation exists_uniformOrdinaryJacquetRealization firstBlockDualFiberIntegral_reflection firstBlockDualFiberIntegral_reflection_on_slice firstBlockDualFiberIntegrand firstBlockDualFiberIntegrand_reflection firstBlockFiberIntegrand firstBlockReflectedColumnNormProfile firstBlockReflectedRowAverage firstBlockReflectedRowAverage_column_control firstBlockReflectedRowAverage_mk_on_slice firstBlockReflectedRowAverage_product_control firstBlockReflectedRowAverage_stronglyMeasurable firstBlockReflectedSmallCoefficient firstBlockReflectedSmallCoefficient_eq_sliceIntegral firstBlockReflectionDensity firstBlockReflectionDensity_nonneg firstBlockRowJacobian firstBlockUpperCoefficient firstBlockUpperCoefficient_eq_small firstBlockUpperCoefficient_eq_small_of_whittakerType firstBlockUpperRowAverage firstBlockUpperRowAverage_eq firstBlockUpperValue firstBlockUpperValue_fiber firstBlock_small_laurent_identity firstCoordinatesBorel firstCoordinatesLocalField firstCoordinatesMatrixBorel firstCoordinatesMeasurable firstCoordinatesSecondCountable firstCoordinatesTopology firstCoordinatesValuation instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_firstBlockRowChange_iff integrable_rectangularBorelMeasure integral_firstBlockReflectedRectangle integral_firstBlockRowChange integral_firstBlockUpperValue integrandBridgeMeasurable integrandBridgeTopology rectangularBorelMeasure rectangularMeasure_map_firstBlockReflectedRectangle rectangularMeasure_map_firstBlockRowChange reflectionAverageBorel reflectionAverageCountable reflectionAverageGLBorel reflectionAverageGLMeasurable reflectionAverageGLTopology reflectionAverageLocalField reflectionAverageMatrixBorel reflectionAverageMatrixCountable reflectionAverageMeasurable reflectionAverageNBorel reflectionAverageNMeasurable reflectionAverageNQBorel reflectionAverageNQMeasurable reflectionAverageTopology reflectionAverageValuation reflectionCoefficientGLBorel reflectionCoefficientGLMeasurable reflectionCoefficientGLTopology reflectionCoefficientLocalField reflectionCoefficientMeasurable reflectionCoefficientNBorel reflectionCoefficientNMeasurable reflectionCoefficientNQMeasurable reflectionCoefficientTopology reflectionCoefficientValuation reflectionIntegrandLocalField reflectionIntegrandTopology reflectionIntegrandValuation reflectionMeasureBorel reflectionMeasureCountable reflectionMeasureLocalField reflectionMeasureMatrixBorel reflectionMeasureMeasurable reflectionMeasureT2 reflectionMeasureTopology reflectionMeasureValuation smallLaurentGLBorel smallLaurentGLMeasurable smallLaurentGLTopology smallLaurentLocalField smallLaurentMeasurable smallLaurentNBorel smallLaurentNMeasurable smallLaurentNQMeasurable smallLaurentTopology smallLaurentValuation unequalRankIntegrandAt_mk unequalRankSliceCoefficientAt_eq_integral upperSliceConverges upperSliceConvergesAt
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement measurePreserving_rectangular_mul_mul padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right rectangularFourierIntegral_comp_mul_mul rectangularFourierIntegral_translate_decomposition rectangularPairing_mul_mul
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice isClosed_mixedSubgroup measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mk_mem_determinantSlice normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding FirstBlockDensityStatement LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockDensity firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk iUnion_determinantSlice integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurePreserving_radicalChange mem_determinantSlice mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice pairwise_disjoint_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding dualIntegrand_integrableOn_slice dualSmallIntegral_series firstBlockCoefficient firstBlockCoefficient_apply firstBlockCoefficient_lowerRadical_mul inv_leviHalfModulus_blockPair_one measurePreserving_reflectionQuotient reflectionQuotient_mem_determinantSlice scalarSection_firstBlockEmbedding_mul scalarSection_lowerRadical_mul setIntegral_determinantSlice_reflectionQuotient smallIntegral_series smallIntegrand_integrableOn_slice tensorContraction_blockTensor_blockPair_one unequalRankIntegrandAt unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient unequalRankSliceCoefficientAt unequalRank_sliceExpansion
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent hiding unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient
open Langlands.QuotientIntegration

universe uF uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance reflectionAverageT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance reflectionAverageCountable : SecondCountableTopology F := (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance reflectionAverageMeasurable : MeasurableSpace F := borel _
local instance reflectionAverageBorel : BorelSpace F := ⟨rfl⟩
local instance reflectionAverageMatrixBorel (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F))
local instance reflectionAverageMatrixCountable (a b : ℕ) : SecondCountableTopology (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F))
local instance reflectionAverageGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F) := borel _
local instance reflectionAverageGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F) := ⟨rfl⟩
local instance reflectionAverageGLTopology (a : ℕ) : IsTopologicalGroup (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup a
local instance reflectionAverageGLCountable (a : ℕ) : SecondCountableTopology (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology a
local instance reflectionAverageNMeasurable (a : ℕ) : MeasurableSpace (upperUnipotent a F) := borel _
local instance reflectionAverageNBorel (a : ℕ) : BorelSpace (upperUnipotent a F) := ⟨rfl⟩
local instance reflectionAverageNQMeasurable (a : ℕ) : MeasurableSpace (LeftUnipotentQuotient a F) := borel _
local instance reflectionAverageNQBorel (a : ℕ) : BorelSpace (LeftUnipotentQuotient a F) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable {ψ : UnitaryAdditiveCharacter F}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F)

/-- The actual reflected small rectangle average with its spectral factor. -/
def firstBlockReflectedRowAverage (d : ℤ)
    (q : LeftUnipotentQuotient (m 0) F)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F) : ℂ :=
  determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
      (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
    ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) ^ d *
    ∫ z, firstBlockDualFiberIntegrand F h j k ell f Wtest 0 Y g z
      (reflectionQuotient (m 0) q) ∂rectangularMeasure ν k (m 0 + 1)

/-- The remaining-column norm profile of the actual reflected row average. -/
def firstBlockReflectedColumnNormProfile (d : ℤ)
    (q : LeftUnipotentQuotient (m 0) F)
    (g : GeneralLinear (t + 1) F) : ℝ :=
  ∫ Y, ‖firstBlockReflectedRowAverage F h j k ell f Wtest ν d q Y g‖
    ∂rectangularMeasure ν j (m 1 + 1)

/-- Joint continuity of the reflected integrand descends through the open
quotient map; its representative formula is the actual lower test matrix. -/
theorem continuous_firstBlockDualFiberIntegrand_reflection
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0))
    (g : GeneralLinear (t + 1) F) :
    Continuous (fun z : LeftUnipotentQuotient (m 0) F ×
        (Matrix (Fin j) (Fin (m 1 + 1)) F ×
          Matrix (Fin k) (Fin (m 0 + 1)) F) =>
      firstBlockDualFiberIntegrand F h j k ell f Wtest 0 z.2.1 g z.2.2
        (reflectionQuotient (m 0) z.1)) := by
  apply ((leftQuotient_isOpenQuotientMap (upperUnipotent (m 0 + 1) F)).prodMap
    IsOpenQuotientMap.id).isQuotientMap.continuous_iff.mpr
  change Continuous (fun z : GeneralLinear (m 0 + 1) F ×
      (Matrix (Fin j) (Fin (m 1 + 1)) F ×
        Matrix (Fin k) (Fin (m 0 + 1)) F) =>
    firstBlockDualFiberIntegrand F h j k ell f Wtest 0 z.2.1 g z.2.2
      (reflectionQuotient (m 0) (Quotient.mk _ z.1)))
  simp_rw [firstBlockDualFiberIntegrand_reflection]
  have hsmall : Continuous (firstBlockCoefficient ell f g).val.val := by
    obtain ⟨v, hv⟩ := modelMap_surjective (σ 0) (ell 0) (firstBlockCoefficient ell f g)
    rw [← hv]
    exact (matrixCoefficient_isLocallyConstant (σ 0) (ell 0).val v (hσ v)).continuous
  have hx : Continuous (fun z : GeneralLinear (m 0 + 1) F ×
      (Matrix (Fin j) (Fin (m 1 + 1)) F ×
        Matrix (Fin k) (Fin (m 0 + 1)) F) =>
      firstBlockReflectedRectangle z.1 z.2.2) :=
    (continuous_const.matrix_mul (Units.continuous_val.comp continuous_fst)).matrix_mul
      continuous_snd.snd.matrix_transpose
  have hY : Continuous (fun Y : Matrix (Fin j) (Fin (m 1 + 1)) F =>
      Y.submatrix Fin.rev Fin.rev) := by fun_prop
  have hm := (TwoBlockDominantRectangular.continuous_matrix h rfl).comp
    ((((continuous_firstBlockEmbedding h F).comp continuous_fst).mul_const g).prodMk
      (hx.prodMk (hY.comp continuous_snd.fst)))
  exact ((hW.comp hm).mul (hsmall.comp continuous_fst)).mul
    ((continuous_adjacentRank_determinantWeight F (m 0 + 1)
      (-(0 - ((k + (m 1 + 1 + j) + 1 : ℕ) : ℂ) / 2))).comp continuous_fst)

/-- Joint measurability of the actual quotient/column average needs no
measurable choice of representatives. -/
theorem firstBlockReflectedRowAverage_stronglyMeasurable
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0)) (d : ℤ)
    (g : GeneralLinear (t + 1) F) :
    StronglyMeasurable (fun z : LeftUnipotentQuotient (m 0) F ×
        Matrix (Fin j) (Fin (m 1 + 1)) F =>
      firstBlockReflectedRowAverage F h j k ell f Wtest ν d z.1 z.2 g) := by
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hi := (continuous_firstBlockDualFiberIntegrand_reflection
    F h j k ell f Wtest hW hσ g).measurable.stronglyMeasurable
  have hm := hi.comp_measurable
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact hm.integral_prod_right'.const_mul _

/-- The positive real density in the lower first-block slice tower. -/
def firstBlockReflectionDensity (d : ℤ) : ℝ :=
  ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
    (-(d * ((m 1 + 1 : ℕ) : ℤ)))

theorem firstBlockReflectionDensity_nonneg (d : ℤ) :
    0 ≤ firstBlockReflectionDensity F (m := m) d :=
  zpow_nonneg (Nat.cast_nonneg _) _

/-- The exact coefficient calculation at a representative on the small slice. -/
theorem firstBlockReflectedRowAverage_mk_on_slice
    (d : ℤ) (v : GeneralLinear (m 0 + 1) F)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F)
    (hv : (Quotient.mk _ v : LeftUnipotentQuotient (m 0) F) ∈
      Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d) :
    firstBlockReflectedRowAverage F h j k ell f Wtest ν d (Quotient.mk _ v) Y g =
      (firstBlockReflectionDensity F (m := m) d : ℂ) *
        ∫ X, Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernel ell f Wtest rfl 0
          (firstBlockEmbedding h F v * g) X (Y.submatrix Fin.rev Fin.rev)
          ∂rectangularMeasure ν (m 0 + 1) k :=
  firstBlockDualFiberIntegral_reflection_on_slice F h j k ell f Wtest ν d Y g v hv

/-- Genuine lower rectangle convergence controls the remaining columns of
the actual reflected average, with the integral of the raw norm retained. -/
theorem firstBlockReflectedRowAverage_column_control
    (d : ℤ) (q : LeftUnipotentQuotient (m 0) F)
    (g : GeneralLinear (t + 1) F)
    (hq : q ∈ Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d)
    (hi : Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientFiberIntegrable ν ell f Wtest rfl 0
      (firstBlockFiberPoint F h q g)) :
    Integrable (fun Y => firstBlockReflectedRowAverage F h j k ell f Wtest ν d q Y g)
      (rectangularMeasure ν j (m 1 + 1)) ∧
    firstBlockReflectedColumnNormProfile F h j k ell f Wtest ν d q g ≤
      firstBlockReflectionDensity F (m := m) d *
        Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientNormProfile ν ell f Wtest rfl 0
          (firstBlockFiberPoint F h q g) ∧
    (∫ Y, firstBlockReflectedRowAverage F h j k ell f Wtest ν d q Y g
      ∂rectangularMeasure ν j (m 1 + 1)) =
      (firstBlockReflectionDensity F (m := m) d : ℂ) *
        Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientKernel ν ell f Wtest rfl 0
          (firstBlockFiberPoint F h q g) := by
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  induction q using Quotient.inductionOn with
  | h v =>
    rw [firstBlockFiberPoint_mk] at hi ⊢
    change Integrable
      (fun z : TwoBlockDominantRectangular.Rectangles m j k F =>
        Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernel ell f Wtest rfl 0
          (firstBlockEmbedding h F v * g) z.1 z.2)
      ((rectangularMeasure ν (m 0 + 1) k).prod (rectangularMeasure ν j (m 1 + 1))) at hi
    let H := fun Y : Matrix (Fin j) (Fin (m 1 + 1)) F =>
      ∫ X, Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernel ell f Wtest rfl 0
        (firstBlockEmbedding h F v * g) X Y
        ∂rectangularMeasure ν (m 0 + 1) k
    have he (Y : Matrix (Fin j) (Fin (m 1 + 1)) F) :
        firstBlockReflectedRowAverage F h j k ell f Wtest ν d (Quotient.mk _ v) Y g =
          (firstBlockReflectionDensity F (m := m) d : ℂ) *
            H (Y.submatrix Fin.rev Fin.rev) :=
      firstBlockReflectedRowAverage_mk_on_slice F h j k ell f Wtest ν d v Y g hq
    have hH : Integrable H (rectangularMeasure ν j (m 1 + 1)) :=
      hi.integral_prod_right
    have hHr := (integrable_firstBlockRectangleReversal_iff F ν j (m 1 + 1) H).mpr hH
    have hB : Integrable (fun Y =>
        firstBlockReflectedRowAverage F h j k ell f Wtest ν d (Quotient.mk _ v) Y g)
        (rectangularMeasure ν j (m 1 + 1)) := by
      simpa only [he] using hHr.const_mul (firstBlockReflectionDensity F (m := m) d : ℂ)
    refine ⟨hB, ?_, ?_⟩
    · have hn := firstBlockReflectionDensity_nonneg F (m := m) d
      calc
        _ = firstBlockReflectionDensity F (m := m) d *
            ∫ Y, ‖H Y‖ ∂rectangularMeasure ν j (m 1 + 1) := by
          simp only [firstBlockReflectedColumnNormProfile, he, norm_mul,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
          rw [integral_const_mul,
            integral_firstBlockRectangleReversal F ν j (m 1 + 1) (fun Y => ‖H Y‖)]
        _ ≤ firstBlockReflectionDensity F (m := m) d *
            ∫ Y, ∫ X, ‖Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernel ell f Wtest rfl 0
              (firstBlockEmbedding h F v * g) X Y‖
                ∂rectangularMeasure ν (m 0 + 1) k
                ∂rectangularMeasure ν j (m 1 + 1) := by
          apply mul_le_mul_of_nonneg_left _ hn
          exact integral_mono hH.norm hi.norm.integral_prod_right
            (fun Y => norm_integral_le_integral_norm _)
        _ = _ := by
          rw [Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientNormProfile_mk]
          congr 1
          exact (integral_prod_symm _ hi.norm).symm
    · simp_rw [he]
      rw [integral_const_mul, integral_firstBlockRectangleReversal,
        Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientKernel_mk]
      congr 1
      exact (integral_prod_symm _ hi).symm

/-- The actual lower raw norm supplies quotient/column product convergence.
Fubini then identifies the integrated reflected coefficient with the actual
unweighted lower first-block average and its positive density. -/
theorem firstBlockReflectedRowAverage_product_control
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0))
    (μ : Measure (LeftUnipotentQuotient (m 0) F)) [SFinite μ]
    (hμ : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) μ)
    (hInv : NormOneRightInvariant F (m 0) μ)
    (d : ℤ) (g : GeneralLinear (t + 1) F)
    (hrect : ∀ᵐ q ∂μ.restrict
        (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d),
      Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientFiberIntegrable ν ell f Wtest rfl 0
        (firstBlockFiberPoint F h q g))
    (hN : Integrable (fun q => Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientNormProfile
      ν ell f Wtest rfl 0 (firstBlockFiberPoint F h q g))
      (μ.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d))) :
    Integrable (fun z : LeftUnipotentQuotient (m 0) F ×
        Matrix (Fin j) (Fin (m 1 + 1)) F =>
      firstBlockReflectedRowAverage F h j k ell f Wtest ν d z.1 z.2 g)
      ((μ.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d)).prod
        (rectangularMeasure ν j (m 1 + 1))) ∧
    Integrable (fun Y => firstBlockReflectedSmallCoefficient F h j k ell f Wtest ν μ d Y g)
      (rectangularMeasure ν j (m 1 + 1)) ∧
    (∫ Y, firstBlockReflectedSmallCoefficient F h j k ell f Wtest ν μ d Y g
      ∂rectangularMeasure ν j (m 1 + 1)) =
      (firstBlockReflectionDensity F (m := m) d : ℂ) *
        firstBlockAverage F h μ hInv d
          (Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientKernel ν ell f Wtest rfl 0)
          (Quotient.mk _ g) := by
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hm := firstBlockReflectedRowAverage_stronglyMeasurable F h j k ell f Wtest ν hW hσ d g
  have hmem := ae_restrict_mem (μ := μ)
    (Langlands.AllField.RankinSelberg.measurableSet_determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d)
  have hp : Integrable
      (fun q => firstBlockReflectedColumnNormProfile F h j k ell f Wtest ν d q g)
      (μ.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d)) := by
    apply (hN.const_mul (firstBlockReflectionDensity F (m := m) d)).mono'
      hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hmem, hrect] with q hq hqr
    have hn : 0 ≤ firstBlockReflectedColumnNormProfile F h j k ell f Wtest ν d q g :=
      integral_nonneg (fun _ => norm_nonneg _)
    change ‖firstBlockReflectedColumnNormProfile F h j k ell f Wtest ν d q g‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact (firstBlockReflectedRowAverage_column_control
      F h j k ell f Wtest ν d q g hq hqr).2.1
  have hi : Integrable (fun z : LeftUnipotentQuotient (m 0) F ×
        Matrix (Fin j) (Fin (m 1 + 1)) F =>
      firstBlockReflectedRowAverage F h j k ell f Wtest ν d z.1 z.2 g)
      ((μ.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d)).prod
        (rectangularMeasure ν j (m 1 + 1))) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨?_, hp⟩
    filter_upwards [hmem, hrect] with q hq hqr
    exact (firstBlockReflectedRowAverage_column_control
      F h j k ell f Wtest ν d q g hq hqr).1
  have he (Y : Matrix (Fin j) (Fin (m 1 + 1)) F) :
      firstBlockReflectedSmallCoefficient F h j k ell f Wtest ν μ d Y g =
        ∫ q in Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d,
          firstBlockReflectedRowAverage F h j k ell f Wtest ν d q Y g ∂μ :=
    firstBlockReflectedSmallCoefficient_eq_sliceIntegral F h j k ell f Wtest ν μ hμ d Y g
  refine ⟨hi, ?_, ?_⟩
  · simpa only [he] using hi.integral_prod_right
  · simp_rw [he]
    rw [← integral_integral_swap hi, Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.firstBlockAverage_mk,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hmem, hrect] with q hq hqr
    exact (firstBlockReflectedRowAverage_column_control
      F h j k ell f Wtest ν d q g hq hqr).2.2

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
