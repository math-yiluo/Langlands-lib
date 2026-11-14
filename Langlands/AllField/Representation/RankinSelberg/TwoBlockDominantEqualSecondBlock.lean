import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualSecondBlock
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDualJacquet
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualDuality
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualFirstBlock
/-! # The actual reversed first-block law at equal rank -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualFirstBlockCoefficientLaw EqualLowerFourierCoefficientLaw EqualTwoSidedFirstBlockLaws determinantComplexPower_inverseTranspose determinantComplexPower_weylLong dualJacquetLocalField dualJacquetTopology dualJacquetValuation equalDualityBorel equalDualityGLBorel equalDualityGLMeasurable equalDualityLocalField equalDualityLowerBorel equalDualityLowerMeasurable equalDualityMeasurable equalDualityQuotientMeasurable equalDualityTopology equalDualityUnipotentBorel equalDualityUnipotentMeasurable equalDualityValuation equalFirstBlockBorel equalFirstBlockGLBorel equalFirstBlockGLMeasurable equalFirstBlockLocalField equalFirstBlockLowerMeasurable equalFirstBlockLowerSeries equalFirstBlockMeasurable equalFirstBlockQuotientMeasurable equalFirstBlockSecondCountable equalFirstBlockTopology equalFirstBlockUnipotentBorel equalFirstBlockUnipotentMeasurable equalFirstBlockValuation equalLowerFourierCoefficientLaw equalLowerGroupIntegrand_reversedDual equalLowerIntegrand_reversedDual equalSecondBlockBorel equalSecondBlockGLBorel equalSecondBlockGLMeasurable equalSecondBlockLocalField equalSecondBlockMeasurable equalSecondBlockQuotientMeasurable equalSecondBlockSecondCountable equalSecondBlockTopology equalSecondBlockUnipotentBorel equalSecondBlockUnipotentMeasurable equalSecondBlockValuation exists_equalFirstBlockBound_forOrdinaryFunctional exists_equalFirstBlockCoefficientLaw exists_equalTwoSidedFirstBlockLaws exists_reversedEqualFirstBlockBound instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier lowerInduced_inverseWhittakerType negatedSelfDualHaar negatedSelfDualHaar_val radicalAverage_eq_equalRankIntegrand reversedDualBlocks_whittakerType reversedDualSectionEquiv_ordinary reversedDual_oppositeTwistBlocks secondDual_oppositeTwistFunctional_val unfoldedJacquetSeries unfoldedJacquetSeries_eq
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
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff determinantWeight_lowerBlockUnipotent_mul dualKernelLocalField dualKernelMeasurable dualKernelTopology dualKernelValuation dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation fiberIntegrable_lowerBlockUnipotent_mul_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_standard_iff kernel_covariance kernel_eq kernel_reversedDual measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_reversedDual quotientNormProfile quotientNormProfile_mk rawKernel rawKernel_covariance rawKernel_reversedDual rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_reversedDual representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul reversedDualSectionEquiv reversedDualSectionEquiv_scalar standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance equalSecondBlockT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance equalSecondBlockSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance equalSecondBlockMeasurable : MeasurableSpace F := borel _
local instance equalSecondBlockBorel : BorelSpace F := ⟨rfl⟩
local instance equalSecondBlockGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance equalSecondBlockGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance equalSecondBlockUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance equalSecondBlockUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance equalSecondBlockQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance equalSecondBlockQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

/-- Every complex determinant power is one on the long Weyl representative. -/
theorem determinantComplexPower_weylLong (n : ℕ) (s : ℂ) :
    (⟨⟩ : LocalFieldData F).determinantComplexPower n s
      (weylLong n F) = 1 := by
  apply Units.ext
  rw [Langlands.LocalFieldData.determinantComplexPower_apply,
    Langlands.LocalFieldData.determinantNorm_coe]
  have hw := TwoBlockFirstBlockLaurent.abv_det_weylLong
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) n
  change (⟨⟩ : LocalFieldData F).normalizedAbs
    (determinant (weylLong n F) : F) = 1 at hw
  simp only [hw, Complex.ofReal_one, Complex.one_cpow, Units.val_one]

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

variable (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))

/-- Dualizing a deformed block preserves the base dual functional's linear map. -/
theorem secondDual_oppositeTwistFunctional_val (u : ℝ) (i : Fin 2) :
    (secondDualFunctional ψ (twoBlockOppositeTwistBlocks F m τ u i)
      (twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))).val =
      (secondDualFunctional ψ (τ i) (ell0 i)).val := by
  ext v
  change (ell0 i).val
      (twoBlockOppositeTwistBlocks F m τ u i (weylLong (m i + 1) F) v) =
    (ell0 i).val (τ i (weylLong (m i + 1) F) v)
  change (ell0 i).val
      (((⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
        (if i = 0 then -(u : ℂ) else (u : ℂ))
        (weylLong (m i + 1) F) : ℂ) •
        τ i (weylLong (m i + 1) F) v) = _
  rw [determinantComplexPower_weylLong, Units.val_one, one_smul]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F) V)
  (lambda : glFunctionals ψ t π)

/-- The first-block bound also works for any equal block presentation and any
functional realizing the ordinary Jacquet function. -/
theorem exists_equalFirstBlockBound_forOrdinaryFunctional
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 0))]
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hlambda : lambda.val ≠ 0)
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      ∀ (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)),
        σ = twoBlockOppositeTwistBlocks F m τ u →
      ∀ (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)),
        (∀ i, (ell i).val = (ell0 i).val) →
      ∀ (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ)),
        (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
          (g : GeneralLinear (t + 1) F),
          J.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ g f) =
            Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val)
              (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g) →
      ∀ (μN : Measure (LeftUnipotentQuotient t F))
        (μA : Measure (LeftUnipotentQuotient (m 0) F)),
        IsCompatible (upperUnipotent (t + 1) F)
          (generalLinearHaar F t) (unipotentHaar F t) μN →
        IsCompatible (upperUnipotent (m 0 + 1) F)
          (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) μA →
        EqualFirstBlockCoefficientLaw F h ψ ν π lambda σ ell J μN μA := by
  obtain ⟨_, _, _, _, hFirst⟩ :=
    twoBlockFirstBlockLaurentIdentity.{uF,uV,uW} F ψ ν t m h
  obtain ⟨Cfirst, hCfirst⟩ := hFirst π hπ lambda τ hτ ell0
  refine ⟨Cfirst, fun u hu σ hσ ell hell J hJ μN μA hμN hμA => ?_⟩
  subst σ
  have hellEq : ell = fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i) := by
    funext i
    exact Subtype.ext (hell i)
  subst ell
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  obtain ⟨_, _, _, _, hLaurent⟩ := hCfirst u hu μN μA hμN hμA
  have hσ0 : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σu 0) :=
    (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u 0 _).2
      ((isOfWhittakerType_standard_iff_inverse ψ (τ 0)).1 (hτ 0))
  have heq := unequalRankFunctionalEquation F (⟨⟩ : LocalFieldData F) (m 0) t
    (firstBlock_lt_total h) ψ μA hμA ν.val ν.property V (W 0) π (σu 0)
    hπ hσ0 lambda (ellu 0) hlambda (hell0 0)
  obtain ⟨c, d, hEpsilon⟩ := exists_unequalRankEpsilonEquation_iff.mpr heq
  obtain ⟨ζ, P, Pdual, hζ, hBody, hLaw⟩ := hLaurent c d hEpsilon
  refine ⟨ζ, c, d, P, Pdual, hEpsilon, hζ,
    fun j k hr => ⟨(hBody j k hr).1, (hBody j k hr).2.1⟩, ?_⟩
  intro f Wtest Φ
  have ha := hLaw f Wtest Φ
  change _ = _ at ha
  change _ = _
  rw [← unfoldedJacquetSeries_eq F h ψ σu ellu
    (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) μN J hJ f Wtest.val Φ]
  exact ha

set_option maxHeartbeats 1600000 in
/-- The fixed section equivalence used by the Fourier law also realizes the
transported second-dual functional by the ordinary reversed Jacquet integral. -/
theorem reversedDualSectionEquiv_ordinary
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsSmooth (σ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
    (hJ : ∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
      (g : GeneralLinear (t + 1) F),
      J.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ g f) =
        Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val)
          (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g) :
    let E := reversedDualSectionEquiv F h σ hσ
    let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
    let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
    let JD := transportedSecondDualFunctional ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E J
    ∀ (fD : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F (reverse_sum h) σD)
      (g : GeneralLinear (t + 1) F),
      JD.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD g fD) =
        Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction (ψ.scale (-1)) (fun i => (ellD i).val)
          (rectangularMeasure ν.val (m 1 + 1) (m 0 + 1)) fD g := by
  dsimp only
  let E := reversedDualSectionEquiv F h σ hσ
  intro fD g
  have hh := transportedSecondDualFunctional_coefficient ψ
    (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E J (E.symm fD)
  have hg := congrArg (fun Z : InverseWhittakerFunctions (ψ.scale (-1)) t => Z.val g) hh
  simp only [E.apply_symm_apply] at hg
  change (transportedSecondDualFunctional ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E J).val
    (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h)
      (fun i => inverseTransposePullback (σ i.rev)) g fD) =
    J.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ
    (weylLong (t + 1) F * inverseTranspose (t + 1) F g)
    (E.symm fD)) at hg
  rw [hg, hJ]
  have hE := Classical.choose_spec (twoBlockDualSectionJacquet F t m h W σ hσ)
  obtain ⟨_, _, _, _, _, hjac⟩ := (hE.2.2 ψ ell).2.2 ν.val
  have hFinal := (hjac (E.symm fD) g).symm
  change Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val)
      (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) (E.symm fD)
      (weylLong (t + 1) F * inverseTranspose (t + 1) F g) =
    Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction (ψ.scale (-1))
      (fun i => (secondDualFunctional ψ (σ i.rev) (ell i.rev)).val)
      (rectangularMeasure ν.val (m 1 + 1) (m 0 + 1)) (E (E.symm fD)) g at hFinal
  simpa only [E.apply_symm_apply] using hFinal

set_option maxHeartbeats 1600000 in
/-- Above one bound the actual reversed first-block law holds for the fixed
transported second-dual functional, at the original real deformation parameter. -/
theorem exists_reversedEqualFirstBlockBound
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 1))]
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hlambda : lambda.val ≠ 0)
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      let σu := twoBlockOppositeTwistBlocks F m τ u
      let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
      let hσu : ∀ i, IsSmooth (σu i) := fun i =>
        ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i)).1.1
      let E := reversedDualSectionEquiv F h σu hσu
      let σD := fun i : Fin 2 => inverseTransposePullback (σu i.rev)
      let ellD := fun i : Fin 2 => secondDualFunctional ψ (σu i.rev) (ellu i.rev)
      ∀ J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu),
        (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu)
          (g : GeneralLinear (t + 1) F),
          J.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu g f) =
            Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val)
              (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g) →
        let JD := transportedSecondDualFunctional ψ
          (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu) E J
        ∀ (μN : Measure (LeftUnipotentQuotient t F))
          (μB : Measure (LeftUnipotentQuotient (m 1) F)),
          IsCompatible (upperUnipotent (t + 1) F)
            (generalLinearHaar F t) (unipotentHaar F t) μN →
          IsCompatible (upperUnipotent (m 1 + 1) F)
            (generalLinearHaar F (m 1)) (unipotentHaar F (m 1)) μB →
          EqualFirstBlockCoefficientLaw F (reverse_sum h) (ψ.scale (-1))
            (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
            (firstDualFunctional ψ π lambda) σD ellD JD μN μB := by
  let τD := fun i : Fin 2 => inverseTransposePullback (τ i.rev)
  let ellD0 := fun i : Fin 2 => secondDualFunctional ψ (τ i.rev) (ell0 i.rev)
  have hπD : IsOfWhittakerType t (standardCharacter (ψ.scale (-1)) t)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hτD := reversedDualBlocks_whittakerType F τ ψ hτ
  obtain ⟨Cdual, hCdual⟩ := exists_equalFirstBlockBound_forOrdinaryFunctional F
    (reverse_sum h) (ψ.scale (-1)) (negatedSelfDualHaar F ψ ν) τD ellD0
    (inverseTransposePullback π) (firstDualFunctional ψ π lambda) hπD
    (firstDualFunctional_ne_zero ψ π hlambda) hτD
    (fun i => secondDualFunctional_ne_zero ψ (τ i.rev) (hell0 i.rev))
  refine ⟨Cdual, fun u hu => ?_⟩
  dsimp only
  intro J hJ μN μB hμN hμB
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  let hσu : ∀ i, IsSmooth (σu i) := fun i =>
    ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i)).1.1
  let E := reversedDualSectionEquiv F h σu hσu
  let σD := fun i : Fin 2 => inverseTransposePullback (σu i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σu i.rev) (ellu i.rev)
  let JD := transportedSecondDualFunctional ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu) E J
  have hJD := reversedDualSectionEquiv_ordinary F h ψ ν σu hσu ellu J hJ
  exact hCdual u hu σD (reversedDual_oppositeTwistBlocks F τ u) ellD
    (fun i => secondDual_oppositeTwistFunctional_val F ψ τ ell0 u i.rev)
    JD hJD μN μB hμN hμB

/-- The original first-block equation, the reversed first-block equation
for the same fixed dual section, and its actual lower Fourier law. -/
def EqualTwoSidedFirstBlockLaws
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsSmooth (σ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
    (μN : Measure (LeftUnipotentQuotient t F))
    (μA : Measure (LeftUnipotentQuotient (m 0) F))
    (μB : Measure (LeftUnipotentQuotient (m 1) F)) : Prop :=
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let JD := transportedSecondDualFunctional ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E J
  EqualFirstBlockCoefficientLaw F h ψ ν π lambda σ ell J μN μA ∧
  EqualFirstBlockCoefficientLaw F (reverse_sum h) (ψ.scale (-1))
    (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
    (firstDualFunctional ψ π lambda) σD ellD JD μN μB ∧
  EqualLowerFourierCoefficientLaw F h σ hσ ψ ell ν μN

set_option maxHeartbeats 1600000 in
/-- Above one real bound a nonzero ordinary Jacquet functional satisfies
both actual first-block equations and the fixed-section lower Fourier law,
uniformly over all three compatible quotient measures. -/
theorem exists_equalTwoSidedFirstBlockLaws
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 0))]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 1))]
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hlambda : lambda.val ≠ 0)
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
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
          EqualTwoSidedFirstBlockLaws F h ψ ν π lambda σu hσu ellu Ju μN μA μB := by
  obtain ⟨Coriginal, hOriginal⟩ := exists_equalFirstBlockCoefficientLaw F h ψ ν π
    lambda hπ hlambda τ hτ ell0 hell0
  obtain ⟨Creversed, hReversed⟩ := exists_reversedEqualFirstBlockBound F h ψ ν τ
    ell0 π lambda hπ hlambda hτ hell0
  refine ⟨max Coriginal Creversed, fun u hu => ?_⟩
  dsimp only
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  let hσu : ∀ i, IsSmooth (σu i) := fun i =>
    ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i)).1.1
  have huo : Coriginal < u := lt_of_le_of_lt (le_max_left _ _) hu
  have hur : Creversed < u := lt_of_le_of_lt (le_max_right _ _) hu
  obtain ⟨habs, J, hJ0, hJ, hFirst⟩ := hOriginal u huo
  refine ⟨habs, J, hJ0, hJ, ?_⟩
  intro μN μA μB hμN hμA hμB
  refine ⟨hFirst μN μA hμN hμA, ?_, ?_⟩
  · exact hReversed u hur J hJ μN μB hμN hμB
  · exact equalLowerFourierCoefficientLaw F h σu hσu ψ ellu ν μN hμN

end Langlands.AllField.RankinSelberg.DominantRankTransport
