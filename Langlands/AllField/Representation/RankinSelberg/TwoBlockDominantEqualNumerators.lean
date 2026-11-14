import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualNumerators
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualSecondBlock
/-! # Actual finite numerators at the equal-rank boundary -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualFirstBlockCoefficientLaw EqualFirstBlockFactorCertificate EqualLowerFourierCoefficientLaw EqualTwoBlockFiniteNumerators EqualTwoSidedFirstBlockLaws coe_equalResidueCardinalityUnit determinantComplexPower_inverseTranspose determinantComplexPower_weylLong dualJacquetLocalField dualJacquetTopology dualJacquetValuation equalDualityBorel equalDualityGLBorel equalDualityGLMeasurable equalDualityLocalField equalDualityLowerBorel equalDualityLowerMeasurable equalDualityMeasurable equalDualityQuotientMeasurable equalDualityTopology equalDualityUnipotentBorel equalDualityUnipotentMeasurable equalDualityValuation equalFirstBlockBorel equalFirstBlockGLBorel equalFirstBlockGLMeasurable equalFirstBlockLocalField equalFirstBlockLowerMeasurable equalFirstBlockLowerSeries equalFirstBlockMeasurable equalFirstBlockQuotientMeasurable equalFirstBlockSecondCountable equalFirstBlockTopology equalFirstBlockUnipotentBorel equalFirstBlockUnipotentMeasurable equalFirstBlockValuation equalLowerFourierCoefficientLaw equalLowerGroupIntegrand_reversedDual equalLowerIntegrand_reversedDual equalNumeratorGLBorel equalNumeratorGLMeasurable equalNumeratorLocalField equalNumeratorQuotientMeasurable equalNumeratorTopology equalNumeratorUnipotentBorel equalNumeratorUnipotentMeasurable equalNumeratorValuation equalResidueCardinalityUnit equalSecondBlockBorel equalSecondBlockGLBorel equalSecondBlockGLMeasurable equalSecondBlockLocalField equalSecondBlockMeasurable equalSecondBlockQuotientMeasurable equalSecondBlockSecondCountable equalSecondBlockTopology equalSecondBlockUnipotentBorel equalSecondBlockUnipotentMeasurable equalSecondBlockValuation equalTwoBlockFiniteNumerators_of_laws exists_equalFirstBlockBound_forOrdinaryFunctional exists_equalFirstBlockCoefficientLaw exists_equalTwoBlockFiniteNumerators exists_equalTwoSidedFirstBlockLaws exists_reversedEqualFirstBlockBound instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier lowerInduced_inverseWhittakerType negatedSelfDualHaar negatedSelfDualHaar_val radicalAverage_eq_equalRankIntegrand reversedDualBlocks_whittakerType reversedDualSectionEquiv_ordinary reversedDual_oppositeTwistBlocks secondDual_oppositeTwistFunctional_val unfoldedJacquetSeries unfoldedJacquetSeries_eq
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankTrilinearUniquenessStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement LowerFirstBlockIntegrationInputStatement LowerFirstBlockSliceTowerInputStatement NormalizedProductWhittakerTypeStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockDualSectionJacquetStatement TwoBlockFirstBlockLaurentIdentityStatement TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockFixedSliceUnfoldingStatement TwoBlockJacquetConvergenceStatement TwoBlockLowerFirstBlockQuotientIntegrationStatement TwoBlockLowerFixedSliceConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport assembleLowerFirstBlockQuotientIntegration continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankContinuedForms equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit lowerFirstBlockIntegrationInput_of_sliceTower lowerFirstBlockSliceTowerInput measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockDualSectionJacquet twoBlockFirstBlockLaurentIdentity twoBlockFirstBlockQuotientIntegration twoBlockFixedSliceUnfolding twoBlockJacquetConvergence twoBlockLowerFirstBlockQuotientIntegration twoBlockLowerFixedSliceConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory LaurentPolynomial
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement TwoBlockRowFourierCompanionStatement exists_rowSchwartz_order_lower_bound padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff determinantWeight_lowerBlockUnipotent_mul dualKernelLocalField dualKernelMeasurable dualKernelTopology dualKernelValuation dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation fiberIntegrable_lowerBlockUnipotent_mul_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_standard_iff kernel_covariance kernel_eq kernel_reversedDual measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_reversedDual quotientNormProfile quotientNormProfile_mk rawKernel rawKernel_covariance rawKernel_reversedDual rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_reversedDual representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul reversedDualSectionEquiv reversedDualSectionEquiv_scalar standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance equalNumeratorT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance equalNumeratorSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance equalNumeratorMeasurable : MeasurableSpace F := borel _
local instance equalNumeratorBorel : BorelSpace F := ⟨rfl⟩
local instance equalNumeratorGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance equalNumeratorGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance equalNumeratorUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance equalNumeratorUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance equalNumeratorQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance equalNumeratorQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

/-- The nonzero canonical residue cardinality, as a complex unit. -/
def equalResidueCardinalityUnit : ℂˣ :=
  Units.mk0 ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) (by
    have hq : (⟨⟩ : LocalFieldData F).residueCardinality ≠ 0 :=
      ne_of_gt (lt_trans Nat.zero_lt_one
        (⟨⟩ : LocalFieldData F).residueCardinality_gt_one)
    exact_mod_cast hq)

@[simp]
theorem coe_equalResidueCardinalityUnit :
    (equalResidueCardinalityUnit F : ℂ) =
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) := rfl

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F) V)
  (lambda : glFunctionals ψ t π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))

/-- The complete first-block factor witnesses, retained before all tests. -/
def EqualFirstBlockFactorCertificate
    (μA : Measure (LeftUnipotentQuotient (m 0) F))
    (ζ c : ℂˣ) (d : ℤ) (P Pdual : Polynomial ℂ) : Prop :=
  UnequalRankEpsilonEquation (firstBlock_lt_total h) qF ψ abv μA ν.val
    π (σ 0) lambda (ell 0) c d ∧
  HasModelMinusOneScalar (σ 0) (ell 0) ζ ∧
  ∀ (j k : ℕ) (hr : t = m 0 + (j + k + 1)),
    IsNormalizedGenerator
      (unequalRankValuesAt j k hr qF ψ abv μA
        (rectangularMeasure ν.val j (m 0 + 1)) π (σ 0) lambda (ell 0)) P ∧
    IsNormalizedGenerator
      (dualUnequalRankRationalValuesAt (firstBlock_lt_total h) j k hr
        qF ψ abv μA ν.val π (σ 0) lambda (ell 0)) Pdual

variable (hσ : ∀ i, IsSmooth (σ i))
  (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F))
  (μA : Measure (LeftUnipotentQuotient (m 0) F))
  (μB : Measure (LeftUnipotentQuotient (m 1) F))

/-- Both first-block certificates and their actual finite numerator identities.
The reversed first block has original polynomial `P₂D` and dual polynomial `P₂`. -/
def EqualTwoBlockFiniteNumerators : Prop :=
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let JD := transportedSecondDualFunctional ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E J
  let q := equalResidueCardinalityUnit F
  ∃ (ζ₁ c₁ ζ₂ c₂ : ℂˣ) (d₁ d₂ : ℤ) (P₁ P₁D P₂ P₂D : Polynomial ℂ),
    EqualFirstBlockFactorCertificate F h ψ ν π lambda σ ell μA ζ₁ c₁ d₁ P₁ P₁D ∧
    EqualFirstBlockFactorCertificate F (reverse_sum h) (ψ.scale (-1))
      (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
      (firstDualFunctional ψ π lambda) σD ellD μB ζ₂ c₂ d₂ P₂D P₂ ∧
    ∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule)
      (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F)),
      IsRowFourierPair ψ ν.val Φ Φhat →
      let a : BilateralLaurentSeries :=
        equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μN ψ Wtest.val
        (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f).val Φ
      let aD : BilateralLaurentSeries :=
        equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μN (ψ.scale (-1))
        (firstDualModelMap ψ π lambda Wtest).val
        (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)).val Φhat
      ∃! R : LaurentPolynomial ℂ,
        ofLaurentPolynomial R = (P₁ * P₂).toLaurent • a ∧
        ofLaurentPolynomial (laurentReflection q R) =
          (laurentReflection q
            (↑(clearedProductMultiplierUnit q (ζ₁ ^ t * c₁) d₁
              (ζ₂ ^ t * c₂) d₂)⁻¹ : LaurentPolynomial ℂ) *
                (P₁D * P₂D).toLaurent) • aD

set_option maxHeartbeats 1600000 in
/-- The actual two-sided laws give finite numerators, with their full factor
certificates common to every section, coefficient and Fourier pair. -/
theorem equalTwoBlockFiniteNumerators_of_laws
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    (hμN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) μN)
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hLaws : EqualTwoSidedFirstBlockLaws F h ψ ν π lambda σ hσ ell J μN μA μB) :
    EqualTwoBlockFiniteNumerators F h ψ ν π lambda σ ell hσ J μN μA μB := by
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let JD := transportedSecondDualFunctional ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E J
  let q := equalResidueCardinalityUnit F
  obtain ⟨hOriginal, hReversed, hFourier⟩ := hLaws
  obtain ⟨ζ₁, c₁, d₁, P₁, P₁D, hε₁, hζ₁, hP₁, hFirst⟩ := hOriginal
  obtain ⟨ζ₂, c₂, d₂, P₂D, P₂, hε₂, hζ₂, hP₂, hSecond⟩ := hReversed
  refine ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    ⟨hε₁, hζ₁, hP₁⟩, ⟨hε₂, hζ₂, hP₂⟩, ?_⟩
  intro f Wtest Φ Φhat hpair
  dsimp only
  let a : BilateralLaurentSeries :=
    equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μN ψ Wtest.val
    (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f).val Φ
  let WtestD := firstDualModelMap ψ π lambda Wtest
  let fD := modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)
  let aD : BilateralLaurentSeries :=
    equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μN (ψ.scale (-1))
    WtestD.val fD.val Φhat
  let b := equalFirstBlockLowerSeries F h ψ ν π lambda σ ell μN f Wtest Φ
  let bD := equalFirstBlockLowerSeries F (reverse_sum h) (ψ.scale (-1))
    (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
    (firstDualFunctional ψ π lambda) σD ellD μN (E f) WtestD Φhat
  have ha : HasLowerBoundedSupport a :=
    equalRankSliceSupport F (⟨⟩ : LocalFieldData F) t ψ μN hμN V
      (Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ) π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ)
      hπ (lowerInduced_inverseWhittakerType F h ψ σ hσtype) lambda J Wtest
      (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f) Φ
  have hπD : IsOfWhittakerType t (standardCharacter (ψ.scale (-1)) t)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hσD := reversedDualBlocks_whittakerType F σ ψ hσtype
  have haD : HasLowerBoundedSupport aD :=
    equalRankSliceSupport F (⟨⟩ : LocalFieldData F) t (ψ.scale (-1)) μN hμN V
      (Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F (reverse_sum h) σD) (inverseTransposePullback π)
      (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD) hπD
      (lowerInduced_inverseWhittakerType F (reverse_sum h) (ψ.scale (-1)) σD hσD)
      (firstDualFunctional ψ π lambda) JD WtestD fD Φhat
  have hFirst' :
      Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₁D • b =
        (C ((ζ₁ ^ t * c₁ : ℂˣ) : ℂ) * T d₁ * P₁.toLaurent) • a := by
    simpa only [q, coe_equalResidueCardinalityUnit, Units.val_mul, Units.val_pow_eq_pow_val]
      using hFirst f Wtest Φ
  have hSecond' :
      Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₂ • bD =
        (C ((ζ₂ ^ t * c₂ : ℂˣ) : ℂ) * T d₂ * P₂D.toLaurent) • aD := by
    simpa only [q, coe_equalResidueCardinalityUnit, Units.val_mul, Units.val_pow_eq_pow_val]
      using hSecond (E f) WtestD Φhat
  have hFourier' (k : ℤ) : bD (-k) = (q : ℂ) ^ (-k) * b k := by
    exact (hFourier f Wtest.val Φ Φhat hpair k).2.1
  exact twoBlock_cleared_numerators q (ζ₁ ^ t * c₁) d₁ (ζ₂ ^ t * c₂) d₂
    ha haD hFirst' hSecond' hFourier'

omit σ ell hσ J μN μA μB in
/-- Above one real bound, a nonzero ordinary Jacquet functional supplies both
complete block certificates and finite numerators uniformly in the compatible
quotient measures. No first-block or Fourier identity is a premise. -/
theorem exists_equalTwoBlockFiniteNumerators
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 0))]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 1))]
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hlambda : lambda.val ≠ 0)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      let σu := twoBlockOppositeTwistBlocks F m τ u
      let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
      let hσu : ∀ i, IsSmooth (σu i) := fun i =>
        ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i)).1.1
      let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
      (∀ f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu,
        Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell0 i).val) μR f) ∧
      ∃ Ju : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu),
        Ju.val ≠ 0 ∧
        (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu)
          (g : GeneralLinear (t + 1) F),
          Ju.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu g f) =
            Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val) μR f g) ∧
        ∀ (μN : Measure (LeftUnipotentQuotient t F))
          (μA : Measure (LeftUnipotentQuotient (m 0) F))
          (μB : Measure (LeftUnipotentQuotient (m 1) F)),
          IsCompatible (upperUnipotent (t + 1) F)
            (generalLinearHaar F t) (unipotentHaar F t) μN →
          IsCompatible (upperUnipotent (m 0 + 1) F)
            (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) μA →
          IsCompatible (upperUnipotent (m 1 + 1) F)
            (generalLinearHaar F (m 1)) (unipotentHaar F (m 1)) μB →
          EqualTwoBlockFiniteNumerators F h ψ ν π lambda σu ellu hσu Ju μN μA μB := by
  obtain ⟨Cbound, hCbound⟩ := exists_equalTwoSidedFirstBlockLaws F h ψ ν τ ell0
    π lambda hπ hlambda hτ hell0
  refine ⟨Cbound, fun u hu => ?_⟩
  dsimp only
  obtain ⟨habs, Ju, hJu0, hJu, hLaws⟩ := hCbound u hu
  refine ⟨habs, Ju, hJu0, hJu, ?_⟩
  intro μN μA μB hμN hμA hμB
  exact equalTwoBlockFiniteNumerators_of_laws F h ψ ν π lambda
    (twoBlockOppositeTwistBlocks F m τ u)
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    (fun i => ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2
      (hτ i)).1.1)
    Ju μN μA μB hμN hπ
    (fun i => (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i))
    (hLaws μN μA μB hμN hμA hμB)

end Langlands.AllField.RankinSelberg.DominantRankTransport
