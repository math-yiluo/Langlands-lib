import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockDisintegration
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockIntegrands
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis
/-! # Joined row measures and the actual upper first-block coefficient -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding UpperSliceConverges continuous_diagonalIntegrand continuous_upperAverage determinantWeight_firstBlockEmbedding determinantWeight_lowerRadical disintegrationGLBorel disintegrationGLMeasurable disintegrationLocalField disintegrationMeasurable disintegrationQuotientMeasurable disintegrationTopology disintegrationUpperBorel disintegrationUpperMeasurable disintegrationValuation exists_uniformOrdinaryJacquetRealization firstBlockFiberIntegrand firstBlockRowJacobian firstBlockUpperCoefficient firstBlockUpperCoefficient_eq_small firstBlockUpperCoefficient_eq_small_of_whittakerType firstBlockUpperRowAverage firstBlockUpperRowAverage_eq firstBlockUpperValue firstBlockUpperValue_fiber firstCoordinatesBorel firstCoordinatesLocalField firstCoordinatesMatrixBorel firstCoordinatesMeasurable firstCoordinatesSecondCountable firstCoordinatesTopology firstCoordinatesValuation instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_firstBlockRowChange_iff integrable_rectangularBorelMeasure integral_firstBlockRowChange integral_firstBlockUpperValue integrandBridgeMeasurable integrandBridgeTopology rectangularBorelMeasure rectangularMeasure_map_firstBlockRowChange unequalRankIntegrandAt_mk unequalRankSliceCoefficientAt_eq_integral upperSliceConverges upperSliceConvergesAt
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

universe uF uV uW uA uS

section RowMeasure



end RowMeasure

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance disintegrationSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance disintegrationMeasurable : MeasurableSpace F := borel F
local instance disintegrationBorel : BorelSpace F := ⟨rfl⟩
local instance disintegrationGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance disintegrationGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance disintegrationUpperMeasurable (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance disintegrationUpperBorel (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance disintegrationQuotientMeasurable (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance disintegrationQuotientBorel (n : ℕ) : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

/-- Product convergence at a transported large rank, with no nonvanishing
assumption on either supplied functional. -/
theorem upperSliceConvergesAt {n r : ℕ} (j k : ℕ)
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {S : Type uS} [AddCommGroup S] [Module ℂ S]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) S)
    (lambda : glFunctionals ψ r π) (ell : glInverseFunctionals ψ n ρ)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (Wsmall : (coefficientModel ρ ell).toSubmodule)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hρ : IsOfWhittakerType n (inverseStandardCharacter ψ n) ρ)
    [Measure.IsMulRightInvariant (unipotentHaar F n)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (hμ : QuotientIntegration.IsCompatible (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) μ)
    (ν : AdditiveHaarMeasure F) (d : ℤ) :
    Integrable (fun z : LeftUnipotentQuotient n F ×
        Matrix (Fin j) (Fin (n + 1)) F =>
      unequalRankIntegrandAt F j k hr ψ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        Wtest.val Wsmall.val 0 z.2 z.1)
      ((μ.restrict (determinantSlice (⟨⟩ : LocalFieldData F) n d)).prod
        (rectangularMeasure ν j (n + 1))) := by
  subst r
  exact upperSliceConverges F j k ψ π ρ lambda ell Wtest Wsmall hπ hρ μ hμ ν d

/-- Rank transport commutes with the actual iterated slice coefficient. -/
theorem unequalRankSliceCoefficientAt_eq_integral {n r : ℕ} (j k : ℕ)
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (LeftUnipotentQuotient n F))
    [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ n) (d : ℤ) :
    unequalRankSliceCoefficientAt F j k hr ψ μ ν W W' d =
      ∫ q in determinantSlice (⟨⟩ : LocalFieldData F) n d,
        ∫ X, unequalRankIntegrandAt F j k hr ψ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) W W' 0 X q ∂ν ∂μ := by
  subst r
  rfl

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable {ψ : UnitaryAdditiveCharacter F}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F)

/-- The actual upper row integral evaluated at a representative of the
small quotient. Its representative independence follows below. -/
def firstBlockUpperRowAverage (s : ℂ)
    (q : LeftUnipotentQuotient (m 0) F)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F) : ℂ :=
  ∫ U, firstBlockUpperValue F h j k ell f Wtest s
    (firstBlockEmbedding h F q.out * (lowerRadical h F Z * g))
    (firstBlockColumns h j U Y) ∂rectangularMeasure ν j (m 0 + 1)

/-- The chosen representative disappears after the exact affine row
substitution. The right side uses the actual small quotient integrand. -/
theorem firstBlockUpperRowAverage_eq (s : ℂ)
    (q : LeftUnipotentQuotient (m 0) F)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      ∫ T, unequalRankIntegrandAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        (translateWhittaker ψ (t + (j + k + 1)) Wtest
          (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
            appendIdentity t (j + k + 1) g))
        (firstBlockCoefficient ell f g).val s (firstBlockRows j Z T) q
        ∂rectangularMeasure ν j (m 0 + 1) := by
  unfold firstBlockUpperRowAverage
  rw [integral_firstBlockUpperValue]
  simp only [firstBlockFiberIntegrand, Quotient.out_eq]

/-- The local upper first-block coefficient, retaining both actual
rectangles and the supplied quotient slice. -/
def firstBlockUpperCoefficient
    (μ : Measure (LeftUnipotentQuotient (m 0) F)) (d : ℤ)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F) : ℂ :=
  ∫ Z, ∫ q in determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d,
    firstBlockUpperRowAverage F h j k ell f Wtest ν 0 q Z Y g ∂μ
      ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1)

/-- Product convergence of the actual smaller integrand justifies the row
disintegration; no convergence is deduced from total integral equalities. -/
theorem firstBlockUpperCoefficient_eq_small
    (μ : Measure (LeftUnipotentQuotient (m 0) F)) [SigmaFinite μ] (d : ℤ)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F)
    (hsmall : Integrable
      (fun z : LeftUnipotentQuotient (m 0) F ×
          Matrix (Fin (m 1 + 1 + j)) (Fin (m 0 + 1)) F =>
        unequalRankIntegrandAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          (translateWhittaker ψ (t + (j + k + 1)) Wtest
            (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
              appendIdentity t (j + k + 1) g))
          (firstBlockCoefficient ell f g).val 0 z.2 z.1)
      ((μ.restrict (determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d)).prod
        (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1)))) :
    Integrable (fun Z => ∫ q in determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d,
      firstBlockUpperRowAverage F h j k ell f Wtest ν 0 q Z Y g ∂μ)
        (rectangularMeasure ν (m 1 + 1) (m 0 + 1)) ∧
    firstBlockUpperCoefficient F h j k ell f Wtest ν μ d Y g =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      unequalRankSliceCoefficientAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ μ
        (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1))
        (translateWhittaker ψ (t + (j + k + 1)) Wtest
          (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
            appendIdentity t (j + k + 1) g))
        (firstBlockCoefficient ell f g).val d := by
  have := Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  obtain ⟨hint, heq⟩ := integral_firstBlockJoinedRows ν
    (μ.restrict (determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d))
    (m 0 + 1) (m 1 + 1) j _ hsmall
  simp only [firstBlockRowJoinEquiv_apply] at hint heq
  change Integrable (fun Z => ∫ q, ∫ T,
    unequalRankIntegrandAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      (translateWhittaker ψ (t + (j + k + 1)) Wtest
        (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
          appendIdentity t (j + k + 1) g))
      (firstBlockCoefficient ell f g).val 0 (firstBlockRows j Z T) q
        ∂rectangularMeasure ν j (m 0 + 1)
        ∂μ.restrict (determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d))
    (rectangularMeasure ν (m 1 + 1) (m 0 + 1)) at hint
  constructor
  · simpa only [firstBlockUpperRowAverage_eq, integral_const_mul] using
      hint.const_mul (determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)))
  · unfold firstBlockUpperCoefficient
    simp_rw [firstBlockUpperRowAverage_eq, integral_const_mul]
    congr 1
    rw [unequalRankSliceCoefficientAt_eq_integral]
    exact heq

/-- The actual local upper coefficient equals the actual smaller JPSS
coefficient for the full Whittaker-type inputs, including zero functionals. -/
theorem firstBlockUpperCoefficient_eq_small_of_whittakerType
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F) V)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (hσ : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σ 0))
    (Wmodel : (coefficientModel π lambda).toSubmodule)
    [Measure.IsMulRightInvariant (unipotentHaar F (m 0))]
    (μ : Measure (LeftUnipotentQuotient (m 0) F)) [SigmaFinite μ]
    (hμ : QuotientIntegration.IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) μ)
    (d : ℤ) (Y : Matrix (Fin j) (Fin (m 1 + 1)) F)
    (g : GeneralLinear (t + 1) F) :
    Integrable (fun Z => ∫ q in determinantSlice (⟨⟩ : LocalFieldData F) (m 0) d,
      firstBlockUpperRowAverage F h j k ell f Wmodel.val ν 0 q Z Y g ∂μ)
        (rectangularMeasure ν (m 1 + 1) (m 0 + 1)) ∧
    firstBlockUpperCoefficient F h j k ell f Wmodel.val ν μ d Y g =
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
        (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      unequalRankSliceCoefficientAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ μ
        (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1))
        (translateWhittaker ψ (t + (j + k + 1)) Wmodel.val
          (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
            appendIdentity t (j + k + 1) g))
        (firstBlockCoefficient ell f g).val d := by
  apply firstBlockUpperCoefficient_eq_small
  exact upperSliceConvergesAt F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
    π (σ 0) lambda (ell 0)
    (translateModelEquiv ψ π lambda
      (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
        appendIdentity t (j + k + 1) g) Wmodel)
    (firstBlockCoefficient ell f g) hπ hσ μ hμ ν d

end Padic

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
