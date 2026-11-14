import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockSmallLaurent
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockDisintegration
/-! # The actual smaller Laurent identity on dominant first-block fibers -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding UpperSliceConverges continuous_diagonalIntegrand continuous_upperAverage determinantWeight_firstBlockEmbedding determinantWeight_lowerRadical disintegrationGLBorel disintegrationGLMeasurable disintegrationLocalField disintegrationMeasurable disintegrationQuotientMeasurable disintegrationTopology disintegrationUpperBorel disintegrationUpperMeasurable disintegrationValuation exists_uniformOrdinaryJacquetRealization firstBlockFiberIntegrand firstBlockReflectedSmallCoefficient firstBlockRowJacobian firstBlockUpperCoefficient firstBlockUpperCoefficient_eq_small firstBlockUpperCoefficient_eq_small_of_whittakerType firstBlockUpperRowAverage firstBlockUpperRowAverage_eq firstBlockUpperValue firstBlockUpperValue_fiber firstBlock_small_laurent_identity firstCoordinatesBorel firstCoordinatesLocalField firstCoordinatesMatrixBorel firstCoordinatesMeasurable firstCoordinatesSecondCountable firstCoordinatesTopology firstCoordinatesValuation instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_firstBlockRowChange_iff integrable_rectangularBorelMeasure integral_firstBlockRowChange integral_firstBlockUpperValue integrandBridgeMeasurable integrandBridgeTopology rectangularBorelMeasure rectangularMeasure_map_firstBlockRowChange smallLaurentGLBorel smallLaurentGLMeasurable smallLaurentGLTopology smallLaurentLocalField smallLaurentMeasurable smallLaurentNBorel smallLaurentNMeasurable smallLaurentNQMeasurable smallLaurentTopology smallLaurentValuation unequalRankIntegrandAt_mk unequalRankSliceCoefficientAt_eq_integral upperSliceConverges upperSliceConvergesAt
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
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
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice isClosed_mixedSubgroup measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mk_mem_determinantSlice normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding LowerMixedQuotient continuous_determinantOrder continuous_firstBlockFiberPoint continuous_projectionFromLower continuous_projectionFromMixed continuous_radicalFiberPoint determinantOrder determinantOrder_mk determinantOrder_projectionFromLower determinantOrder_projectionFromMixed determinantOrder_radicalFiberPoint determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice firstBlockAverage firstBlockAverage_mk firstBlockEmbedding_mul_lowerRadical_mul_mixedEmbedding firstBlockFiberIntegral firstBlockFiberIntegral_def firstBlockFiberIntegral_lowerMixedSubgroup_mul firstBlockFiberIntegral_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint firstBlockFiberPoint_lowerRadical_mixedEmbedding_mul firstBlockFiberPoint_mk iUnion_determinantSlice integral_comp_radicalChange isClopen_determinantSlice isClosed_lowerMixedSubgroup lowerBlockUnipotent_le_lowerMixedSubgroup lowerMixedCoordinates lowerMixedCoordinates_lowerProduct lowerMixedDiagonal lowerMixedDiagonal_fst_val lowerMixedDiagonal_lowerProduct lowerMixedDiagonal_snd_val lowerMixedSubgroup lowerMixedSubgroupEquiv lowerMixedSubgroupEquiv_apply_val lowerMixedSubgroupEquiv_mul lowerMixedSubgroupEquiv_symm_apply_fst lowerMixedSubgroupHomeomorph lowerMixedSubgroup_le_normOneSubgroup lowerMixedSubgroup_le_oppositeParabolic lowerMixed_decomposition lowerProduct_lowerMixedCoordinates lowerProduct_mem lowerRadical_mul_leviEmbedding_one_mem measurableSet_determinantSlice measurePreserving_radicalChange mem_determinantSlice mem_lowerMixedSubgroup_iff mixedSubgroup_le_lowerMixedSubgroup mk_mem_determinantSlice pairwise_disjoint_determinantSlice projectionFromLower projectionFromLower_mk projectionFromLower_preimage_determinantSlice projectionFromMixed projectionFromMixed_mk projectionFromMixed_preimage_determinantSlice radicalAverage radicalAverage_mk radicalChange radicalChangeHomeomorph radicalChangeHomeomorph_apply radicalChange_apply radicalFiberIntegral radicalFiberIntegral_def radicalFiberIntegral_lowerMixedSubgroup_mul radicalFiberIntegral_lowerRadical_mixedEmbedding_mul radicalFiberPoint radicalFiberPoint_def radicalFiberPoint_lowerRadical_mixedEmbedding_mul radicalFiberPoint_mem_determinantSlice_iff rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding dualIntegrand_integrableOn_slice dualSmallIntegral_series firstBlockCoefficient firstBlockCoefficient_apply firstBlockCoefficient_lowerRadical_mul inv_leviHalfModulus_blockPair_one scalarSection_firstBlockEmbedding_mul scalarSection_lowerRadical_mul smallIntegral_series smallIntegrand_integrableOn_slice tensorContraction_blockTensor_blockPair_one unequalRankIntegrandAt unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient unequalRankSliceCoefficientAt unequalRank_sliceExpansion
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent hiding unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient
open Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance smallLaurentT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance smallLaurentCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance smallLaurentGLTopology (a : ℕ) : IsTopologicalGroup (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup a
local instance smallLaurentGLCountable (a : ℕ) : SecondCountableTopology (GeneralLinear a F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology a
local instance smallLaurentMeasurable : MeasurableSpace F := borel _
local instance smallLaurentBorel : BorelSpace F := ⟨rfl⟩
local instance smallLaurentGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F) := borel _
local instance smallLaurentGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F) := ⟨rfl⟩
local instance smallLaurentNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F) := borel _
local instance smallLaurentNBorel (a : ℕ) : BorelSpace (upperUnipotent a F) := ⟨rfl⟩
local instance smallLaurentNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance smallLaurentNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F) := borel _
local instance smallLaurentNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable {ψ : UnitaryAdditiveCharacter F}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F)

/-- The reflected, transformed smaller JPSS slice coefficient, with the same
base determinant factor as the actual upper first-block coefficient. -/
def firstBlockReflectedSmallCoefficient
    (μ : Measure (LeftUnipotentQuotient (m 0) F)) (d : ℤ)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F) : ℂ :=
  determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
      (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
    reflectSeries (⟨⟩ : LocalFieldData F).residueCardinality
      (fun n => unequalRankSliceCoefficientAt F k (m 1 + 1 + j)
        (by have := firstBlockSmallRank h j k; omega) (ψ.scale (-1)) μ
        (rectangularMeasure ν k (m 0 + 1))
        (translateWhittaker (ψ.scale (-1)) (t + (j + k + 1))
          (firstDualFunction ψ (t + (j + k + 1))
            (translateWhittaker ψ (t + (j + k + 1)) Wtest
              (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
                appendIdentity t (j + k + 1) g)))
          (blockWeylAt (m 0) (t + (j + k + 1)) (firstBlockSmallRank_lt h j k)))
        (secondDualFunction ψ (m 0) (firstBlockCoefficient ell f g).val) n) d

/-- The actual small functional equation gives the finite Laurent identity
at every remaining-column matrix and base representative. Both normalized
generators are retained, and no bilateral polynomial is cancelled. -/
theorem firstBlock_small_laurent_identity
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F) V)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (hσ : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σ 0))
    (Wmodel : (coefficientModel π lambda).toSubmodule)
    [Measure.IsMulRightInvariant (unipotentHaar F (m 0))]
    (μ : Measure (LeftUnipotentQuotient (m 0) F)) [SigmaFinite μ]
    (hμ : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) μ)
    (ζ cε : ℂˣ) (e : ℤ) (P Pdual : Polynomial ℂ)
    (hP : IsNormalizedGenerator
      (unequalRankValuesAt (m 1 + 1 + j) k (firstBlockSmallRank h j k)
        (⟨⟩ : LocalFieldData F).residueCardinality ψ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μ
        (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1)) π (σ 0) lambda (ell 0)) P)
    (hPd : IsNormalizedGenerator
      (dualUnequalRankRationalValuesAt (firstBlockSmallRank_lt h j k)
        (m 1 + 1 + j) k (firstBlockSmallRank h j k)
        (⟨⟩ : LocalFieldData F).residueCardinality ψ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μ ν π (σ 0) lambda (ell 0)) Pdual)
    (hpairs : ∀ (fs : (coefficientModel π lambda).toSubmodule)
      (ff : (coefficientModel (σ 0) (ell 0)).toSubmodule),
      ∃ R Rdual : RationalFunctions,
        HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
          (unequalRankIntegralAt (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μ
            (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1)) fs.val ff.val) R ∧
        HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
          (dualUnequalRankModelIntegralAt (firstBlockSmallRank_lt h j k)
            (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μ ν π (σ 0)
            lambda (ell 0) fs ff) Rdual ∧
        NormalizedFunctionalEquation (⟨⟩ : LocalFieldData F).residueCardinality
          P Pdual ζ cε (t + (j + k + 1)) e R Rdual)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    let Zlow : BilateralLaurentSeries :=
      fun d => firstBlockReflectedSmallCoefficient F h j k ell f Wmodel.val ν μ d Y g
    let Zup : BilateralLaurentSeries :=
      fun d => firstBlockUpperCoefficient F h j k ell f Wmodel.val ν μ d Y g
    reflectedPolynomial (⟨⟩ : LocalFieldData F).residueCardinality Pdual • Zlow =
      (LaurentPolynomial.C ((ζ : ℂ) ^ (t + (j + k + 1)) * (cε : ℂ)) *
          LaurentPolynomial.T e * P.toLaurent) •
        Zup := by
  dsimp only
  obtain ⟨hlam, hell⟩ := normalizedGenerator_functionals_ne_zero
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
    (m 1 + 1 + j) k (firstBlockSmallRank h j k) hP
  let fs := translateModelEquiv ψ π lambda
    (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
      appendIdentity t (j + k + 1) g) Wmodel
  let ff := firstBlockCoefficient ell f g
  obtain ⟨R, Rd, hR, hRd, hFE⟩ := hpairs fs ff
  have hRm : R ∈ unequalRankValuesAt (m 1 + 1 + j) k (firstBlockSmallRank h j k)
      (⟨⟩ : LocalFieldData F).residueCardinality ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μ
      (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1)) π (σ 0) lambda (ell 0) := by
    rw [unequalRankValuesAt_eq]
    exact ⟨fs, ff, hR⟩
  have hRdm : Rd ∈ dualUnequalRankRationalValuesAt (firstBlockSmallRank_lt h j k)
      (m 1 + 1 + j) k (firstBlockSmallRank h j k)
      (⟨⟩ : LocalFieldData F).residueCardinality ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μ ν π (σ 0) lambda (ell 0) :=
    ⟨fs, ff, hRd⟩
  have heq := smallFE_coefficient_identity (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
    hP hPd hRm hRdm hR hRd hFE
    (smallIntegral_series F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ μ hμ
      inferInstance ν π (σ 0) hπ hσ lambda (ell 0) hlam hell fs ff)
    (dualSmallIntegral_series F (firstBlockSmallRank_lt h j k) (m 1 + 1 + j) k
      (firstBlockSmallRank h j k) ψ μ hμ inferInstance ν π (σ 0) hπ hσ
      lambda (ell 0) hlam hell fs ff)
  have hupper : (fun d => firstBlockUpperCoefficient F h j k ell f Wmodel.val ν μ d Y g) =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) •
      (fun d => unequalRankSliceCoefficientAt F (m 1 + 1 + j) k
        (firstBlockSmallRank h j k) ψ μ (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1))
        fs.val ff.val d) := by
    funext d
    exact (firstBlockUpperCoefficient_eq_small_of_whittakerType F h j k ell f ν
      π lambda hπ hσ Wmodel μ hμ d Y g).2
  rw [hupper]
  let c : ℂ := determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
    (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ))
  change reflectedPolynomial _ Pdual • (c • reflectSeries _ _) =
    (LaurentPolynomial.C ((ζ : ℂ) ^ (t + (j + k + 1)) * (cε : ℂ)) *
      LaurentPolynomial.T e * P.toLaurent) • (c • _)
  rw [smul_comm (reflectedPolynomial _ Pdual) c,
    smul_comm (_ * _ * P.toLaurent) c]
  exact congrArg (fun Z : BilateralLaurentSeries => c • Z) heq

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
