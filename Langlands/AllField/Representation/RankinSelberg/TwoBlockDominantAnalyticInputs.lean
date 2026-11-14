import Langlands.Representation.RankinSelberg.TwoBlockDominantAnalyticInputs
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantSliceConvergence
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasurePackage
/-! # Uniform analytic inputs for the dominant first-block identity -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg.TwoBlockDominantFirstBlock hiding HasUniformAnalyticInputs UpperSliceConverges analyticInputsGLBorel analyticInputsGLGroup analyticInputsGLMeasurable analyticInputsLocalField analyticInputsLowerBorel analyticInputsLowerMeasurable analyticInputsNBorel analyticInputsNMeasurable analyticInputsQBorel analyticInputsQMeasurable analyticInputsT2 analyticInputsTopology analyticInputsValuation compatible_standard_quotients continuous_diagonalIntegrand continuous_upperAverage exists_uniformOrdinaryJacquetRealization exists_uniform_analytic_inputs instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceLeftUnipotentQuotientCarrier instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsTopologicalGroupGeneralLinearCarrier instLocallyCompactSpaceGeneralLinearCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instSecondCountableTopologyCarrier instSecondCountableTopologyGeneralLinearCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_rectangularBorelMeasure rectangularBorelMeasure upperSliceConverges
open Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement exists_rowSchwartz_order_lower_bound padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable IsBlockSumLastEntryBound IsBlockSumRectangularSupport IsCoefficientRectangleGrowth IsKernelNormTorusEnvelope IsLeviFirstInverseEndpointBound IsLeviFirstRectangularSupport IsLeviSecondEndpointBound IsLeviSecondRectangularSupport IsRawKernelTorusMajorant IsTorusBlockSupport IsTorusRectangleBoxSupport IsUniformSliceConvergence KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff ae_quotientFiberIntegrable_spectral_iff append_isEntryBounded append_mem_integralOpen blockSum_mem_integralOpen box_mono box_mul box_neg_transpose box_of_reverse continuous_kernel determinantWeight_lowerBlockUnipotent_mul diagonalRightPermutation_mem_integralOpen dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation endpointBoundsTopology exists_blockSum_last_entry_bound exists_blockSum_rectangular_support exists_box_of_isCompact exists_coefficient_blockSum_rootBounded exists_coefficient_rectangle_growth_uniform exists_kernelNorm_torus_envelope exists_levi_first_inverse_endpoint_bound exists_levi_first_rectangular_support exists_levi_second_endpoint_bound exists_levi_second_rectangular_support exists_rawKernel_torus_majorant exists_reindex_blockSum_last_entry_bound exists_reindex_blockSum_rectangular_support exists_rotated_torus_oppositeCone exists_standard_torus_representative exists_summable_kernelNorm_majorant exists_torus_block_support exists_torus_rectangle_box_support exists_uniform_slice_convergence fiberIntegrable_lowerBlockUnipotent_mul_iff fiberIntegrable_spectral_iff fiber_integrable_normProfile_le_of_box firstEndpointLocalField firstEndpointTopology firstEndpointValuation instIsNonarchimedeanLocalFieldCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier_1 integrableOn_quotientKernel_spectral_iff integrableOn_quotientNormProfile_spectral_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange isEntryBounded_reflected iwasawa_principal_suffix_minor_bound kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_of_summable_torus_bound kernelAbsoluteIntegrable_restrict kernelAbsoluteIntegrable_restrict_spectral_iff kernelAbsoluteIntegrable_standard_iff kernelRegularityBorel kernelRegularityGLBorel kernelRegularityGLLocallyCompact kernelRegularityGLMeasurable kernelRegularityGLSecondCountable kernelRegularityLocalField kernelRegularityMatrixBorel kernelRegularityMatrixSecondCountable kernelRegularityMeasurable kernelRegularitySecondCountable kernelRegularityT2 kernelRegularityTopology kernelRegularityValuation kernelSliceCoefficient kernel_covariance kernel_eq kernel_referenceParameter kernel_spectral matrixGrowthTopology matrixGrowthValuation matrix_isEntryBounded measurableSet_rectangle_box measurable_quotientKernel measurable_quotientNormProfile measurable_representativeKernel measurable_representativeNormProfile measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange mem_box_iff_normalizedAbs mem_box_of_mul_mem_box normEnvelopeBorel normEnvelopeLocalField normEnvelopeMatrixBorel normEnvelopeMatrixSecondCountable normEnvelopeMeasurable normEnvelopeSecondCountable normEnvelopeTopology normEnvelopeValuation normalizedAbs_ratios_of_rootBounded originalConeTopology outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField permutation_mem_integralOpen quotientFiberIntegrable quotientFiberIntegrable_spectral_iff quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_spectral quotientKernel_spectral_onSlice quotientNormProfile quotientNormProfile_mk quotientNormProfile_spectral quotientNormProfile_spectral_onSlice rawKernel rawKernel_covariance rawScalarValue rectangleBoxesBorel rectangleBoxesMeasurable rectangleBoxesTopology rectangleBoxesValuation rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_box rectangleMeasure_box_ne_top rectangleMeasure_real_box rectangleMeasure_real_box_le rectangleMeasure_sigmaFinite rectangleUnipotent_isEntryBounded rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_spectral representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul representativeNormProfile_spectral setIntegral_quotientKernel_spectral sliceConvergenceGLBorel sliceConvergenceGLMeasurable sliceConvergenceLocalField sliceConvergenceLowerBorel sliceConvergenceLowerMeasurable sliceConvergenceMeasurable sliceConvergenceNBorel sliceConvergenceNMeasurable sliceConvergenceQBorel sliceConvergenceQMeasurable sliceConvergenceTopology sliceConvergenceValuation sliceSpectralMeasurable sliceSpectralTopology standardCompatible standardCompatible_sigmaFinite torusMajorantTopology torusMajorantValuation twoBlockDominantBlockSupportLocalInstance1 unequalRankMatrix_last_entry_bound
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance analyticInputsT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance analyticInputsSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance analyticInputsGLGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
local instance analyticInputsGLCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance analyticInputsGLSecondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance analyticInputsMeasurable : MeasurableSpace F := borel _
local instance analyticInputsBorel : BorelSpace F := ⟨rfl⟩
local instance analyticInputsGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F) := borel _
local instance analyticInputsGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance analyticInputsNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent n F) := borel _
local instance analyticInputsNBorel (n : ℕ) :
    BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance analyticInputsQMeasurable (t : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient t F) := borel _
local instance analyticInputsQBorel (t : ℕ) :
    BorelSpace (LeftUnipotentQuotient t F) := ⟨rfl⟩
local instance analyticInputsLowerMeasurable {t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1) :
    MeasurableSpace (LowerQuotient h F) := borel _
local instance analyticInputsLowerBorel {t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1) :
    BorelSpace (LowerQuotient h F) := ⟨rfl⟩

/-- Existence of both exact standard quotient measures is independent of the
sections, representations and additive Haar measure. -/
theorem compatible_standard_quotients (t a : ℕ) :
    ∃ (hN : Measure.IsMulRightInvariant (unipotentHaar F t))
      (hNA : Measure.IsMulRightInvariant (unipotentHaar F a)),
      letI := hN
      letI := hNA
      (∃ νN : Measure (LeftUnipotentQuotient t F),
        IsCompatible (upperUnipotent (t + 1) F)
          (generalLinearHaar F t) (unipotentHaar F t) νN) ∧
      (∃ νA : Measure (LeftUnipotentQuotient a F),
        IsCompatible (upperUnipotent (a + 1) F)
          (generalLinearHaar F a) (unipotentHaar F a) νA) := by
  refine ⟨unipotentHaar_isMulRightInvariant F t,
    unipotentHaar_isMulRightInvariant F a, ?_⟩
  exact ⟨unipotent_compatibleMeasureExists F t,
    unipotent_compatibleMeasureExists F a⟩

variable {t r : ℕ} {m : Fin 2 → ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- All analytic clauses of the first-block target, with one bound and one
ordinary Jacquet functional before every supplied measure and test. -/
def HasUniformAnalyticInputs
    (h : ∑ i, (m i + 1) = t + 1) (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u →
    let σu := twoBlockOppositeTwistBlocks F m τ u
    let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
    let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
    (∀ f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu,
      Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ellu i).val) μR f) ∧
    ∃ J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu),
      ((∀ i, (ell i).val ≠ 0) → J.val ≠ 0) ∧
      (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu)
        (g : GeneralLinear (t + 1) F),
        J.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu g f) =
          Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val) μR f g) ∧
      ∀ (hN : Measure.IsMulRightInvariant (unipotentHaar F t))
        (hNA : Measure.IsMulRightInvariant (unipotentHaar F (m 0))),
        letI := hN
        letI := hNA
        ∀ (νN : Measure (LeftUnipotentQuotient t F))
          (νA : Measure (LeftUnipotentQuotient (m 0) F)),
          IsCompatible (upperUnipotent (t + 1) F)
            (generalLinearHaar F t) (unipotentHaar F t) νN →
          IsCompatible (upperUnipotent (m 0 + 1) F)
            (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) νA →
          let νMinus : Measure (LowerQuotient h F) :=
            Measure.map (lowerToStandard h F).symm νN
          SigmaFinite νN ∧ SigmaFinite νA ∧ SigmaFinite νMinus ∧
          ∀ (j k : ℕ) (hr : r = t + (j + k + 1))
            (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu)
            (Wtest : (coefficientModel π lambda).toSubmodule),
            let Wup : WhittakerFunctions ψ (t + (j + k + 1)) := hr ▸ Wtest.val
            let Wjac := (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu) J f).val
            let μrect := rectangularMeasure ν.val j (t + 1)
            let A := unequalRankAverage F j k ψ
              (rectangularBorelMeasure F ν.val j (t + 1)) Wup Wjac 0
            let K := quotientKernel ν.val ellu f Wtest.val hr 0
            let Nprofile := quotientNormProfile ν.val ellu f Wtest.val hr 0
            let Fiber := quotientFiberIntegrable ν.val ellu f Wtest.val hr 0
            Measurable A ∧ Measurable K ∧
            ∀ a : ℤ,
              Integrable (fun z : LeftUnipotentQuotient t F ×
                Matrix (Fin j) (Fin (t + 1)) F =>
                  unequalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
                    j k Wup Wjac 0 z.2 z.1)
                ((νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice
                  (⟨⟩ : LocalFieldData F) t a)).prod μrect) ∧
              Integrable K (νMinus.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h a)) ∧
              Integrable Nprofile (νMinus.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h a)) ∧
              ∀ᵐ z ∂νMinus.restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h a), Fiber z

/-- The maximum of the ordinary Jacquet and raw-norm thresholds proves every
analytic clause without a small-block epsilon premise. -/
theorem exists_uniform_analytic_inputs
    (h : ∑ i, (m i + 1) = t + 1) (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) :
    ∃ C : ℝ, HasUniformAnalyticInputs F h ψ ν π lambda τ ell C := by
  obtain ⟨CJ, hCJ⟩ := exists_uniformOrdinaryJacquetRealization F h ψ ν τ hτ ell
  obtain ⟨CL, hCL⟩ :=
    exists_uniform_slice_convergence ν.val h ψ π hπ lambda τ hτ ell
  refine ⟨max CJ CL, fun u hu => ?_⟩
  obtain ⟨habs, J, hJ0, hJ⟩ := hCJ u ((le_max_left CJ CL).trans_lt hu)
  refine ⟨habs, J, hJ0, hJ, ?_⟩
  intro hN hNA
  let := hN
  let := hNA
  intro νN νA hνN hνA
  have hsf := standardCompatible_sigmaFinite F h hN νN hνN
  have hsfA := Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient.compatibleQuotient_sigmaFinite
    F (m 0) (upperUnipotent (m 0 + 1) F)
      (UpperUnipotent.isClosed (R := F)) _ νA hνA
  refine ⟨hsf.1, hsfA, hsf.2, ?_⟩
  intro j k hr f Wtest
  subst r
  dsimp only
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
  have hσ : IsOfWhittakerType t (inverseStandardCharacter ψ t)
      (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu) :=
    Langlands.AllField.RankinSelberg.DominantRankTransport.lowerInduced_inverseWhittakerType F h ψ σu
      (fun i => (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff
        F m τ u i _).mpr (hτ i))
  obtain ⟨hm, _, hi⟩ :=
    hCL u ((le_max_right CJ CL).trans_lt hu) hN νN hνN f j k rfl Wtest
  refine ⟨(continuous_upperAverage F j k ψ π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu)
      lambda J Wtest (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu) J f)
      hπ hσ.1.1 ν.val 0).measurable, (hm 0).1, fun a => ?_⟩
  refine ⟨upperSliceConverges F j k ψ π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu)
    lambda J Wtest (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu) J f)
    hπ hσ νN hνN ν.val a, ?_⟩
  have hli := hi 0 a
  change Integrable _ _ ∧ Integrable _ _ ∧ _ at hli
  have hμ : Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure F h
      (νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t a)) =
      (Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure F h νN).restrict
        (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h a) :=
    (Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure_restrict F h νN a).symm
  rw [hμ] at hli
  exact hli

end Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock
