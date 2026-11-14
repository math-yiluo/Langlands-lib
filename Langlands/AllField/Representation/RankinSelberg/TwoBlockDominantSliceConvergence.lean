import Langlands.Representation.RankinSelberg.TwoBlockDominantSliceConvergence
import Langlands.AllField.Representation.RankinSelberg.QuotientTorusEnvelope
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantNormEnvelope
/-! # Genuine slice convergence of the actual dominant kernel -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable IsBlockSumLastEntryBound IsBlockSumRectangularSupport IsCoefficientRectangleGrowth IsKernelNormTorusEnvelope IsLeviFirstInverseEndpointBound IsLeviFirstRectangularSupport IsLeviSecondEndpointBound IsLeviSecondRectangularSupport IsRawKernelTorusMajorant IsTorusBlockSupport IsTorusRectangleBoxSupport IsUniformSliceConvergence KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff ae_quotientFiberIntegrable_spectral_iff append_isEntryBounded append_mem_integralOpen blockSum_mem_integralOpen box_mono box_mul box_neg_transpose box_of_reverse continuous_kernel determinantWeight_lowerBlockUnipotent_mul diagonalRightPermutation_mem_integralOpen dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation endpointBoundsTopology exists_blockSum_last_entry_bound exists_blockSum_rectangular_support exists_box_of_isCompact exists_coefficient_blockSum_rootBounded exists_coefficient_rectangle_growth_uniform exists_kernelNorm_torus_envelope exists_levi_first_inverse_endpoint_bound exists_levi_first_rectangular_support exists_levi_second_endpoint_bound exists_levi_second_rectangular_support exists_rawKernel_torus_majorant exists_reindex_blockSum_last_entry_bound exists_reindex_blockSum_rectangular_support exists_rotated_torus_oppositeCone exists_standard_torus_representative exists_summable_kernelNorm_majorant exists_torus_block_support exists_torus_rectangle_box_support exists_uniform_slice_convergence fiberIntegrable_lowerBlockUnipotent_mul_iff fiberIntegrable_spectral_iff fiber_integrable_normProfile_le_of_box firstEndpointLocalField firstEndpointTopology firstEndpointValuation instIsNonarchimedeanLocalFieldCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier_1 integrableOn_quotientKernel_spectral_iff integrableOn_quotientNormProfile_spectral_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange isEntryBounded_reflected iwasawa_principal_suffix_minor_bound kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_of_summable_torus_bound kernelAbsoluteIntegrable_restrict kernelAbsoluteIntegrable_restrict_spectral_iff kernelAbsoluteIntegrable_standard_iff kernelRegularityBorel kernelRegularityGLBorel kernelRegularityGLLocallyCompact kernelRegularityGLMeasurable kernelRegularityGLSecondCountable kernelRegularityLocalField kernelRegularityMatrixBorel kernelRegularityMatrixSecondCountable kernelRegularityMeasurable kernelRegularitySecondCountable kernelRegularityT2 kernelRegularityTopology kernelRegularityValuation kernelSliceCoefficient kernel_covariance kernel_eq kernel_referenceParameter kernel_spectral matrixGrowthTopology matrixGrowthValuation matrix_isEntryBounded measurableSet_rectangle_box measurable_quotientKernel measurable_quotientNormProfile measurable_representativeKernel measurable_representativeNormProfile measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange mem_box_iff_normalizedAbs mem_box_of_mul_mem_box normEnvelopeBorel normEnvelopeLocalField normEnvelopeMatrixBorel normEnvelopeMatrixSecondCountable normEnvelopeMeasurable normEnvelopeSecondCountable normEnvelopeTopology normEnvelopeValuation normalizedAbs_ratios_of_rootBounded originalConeTopology outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField permutation_mem_integralOpen quotientFiberIntegrable quotientFiberIntegrable_spectral_iff quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_spectral quotientKernel_spectral_onSlice quotientNormProfile quotientNormProfile_mk quotientNormProfile_spectral quotientNormProfile_spectral_onSlice rawKernel rawKernel_covariance rawScalarValue rectangleBoxesBorel rectangleBoxesMeasurable rectangleBoxesTopology rectangleBoxesValuation rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_box rectangleMeasure_box_ne_top rectangleMeasure_real_box rectangleMeasure_real_box_le rectangleMeasure_sigmaFinite rectangleUnipotent_isEntryBounded rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_spectral representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul representativeNormProfile_spectral setIntegral_quotientKernel_spectral sliceConvergenceGLBorel sliceConvergenceGLMeasurable sliceConvergenceLocalField sliceConvergenceLowerBorel sliceConvergenceLowerMeasurable sliceConvergenceMeasurable sliceConvergenceNBorel sliceConvergenceNMeasurable sliceConvergenceQBorel sliceConvergenceQMeasurable sliceConvergenceTopology sliceConvergenceValuation sliceSpectralMeasurable sliceSpectralTopology standardCompatible standardCompatible_sigmaFinite torusMajorantTopology torusMajorantValuation twoBlockDominantBlockSupportLocalInstance1 unequalRankMatrix_last_entry_bound
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice quotientIwasawaIntegration rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val unequalRankIwasawaSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement exists_rowSchwartz_order_lower_bound padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding blockRotation_inv_mul_torus compatible_measure_data determinantNorm_torus determinantNorm_torus_bounds diagonalDensity diagonalDensity_le diagonalDensity_nonneg exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_integrand_torus_majorant exists_rotated_section_growth exists_section_growth exists_standard_functional_growth exists_summable_integrand_majorant instBorelSpaceCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_4 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integrable_lowerMeasure_iff integral_lowerMeasure integrand_standard_mk isEntryBounded_torus lowerMeasure lowerMeasure_restrict measureTransportFieldT2 measureTransportFieldTopology measureTransportFieldValuation measureTransportGeneralLinearGroup measureTransportGeneralLinearLocallyCompact measureTransportGeneralLinearSecondCountable measureTransportLocalField normalizedAbs_uniformizer_zpow sigmaFinite_lowerMeasure torusLevi torusLevi_embedding torusLevi_entryBounded torusLevi_inv_halfModulus_le torusLevi_rotated_twist
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped BigOperators NNReal ENNReal

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance sliceConvergenceMeasurable : MeasurableSpace F := borel _
local instance sliceConvergenceGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F) := borel _
local instance sliceConvergenceGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance sliceConvergenceNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent n F) := borel _
local instance sliceConvergenceNBorel (n : ℕ) :
    BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance sliceConvergenceQMeasurable (t : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient t F) := borel _
local instance sliceConvergenceQBorel (t : ℕ) :
    BorelSpace (LeftUnipotentQuotient t F) := ⟨rfl⟩
local instance sliceConvergenceLowerMeasurable {t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1) :
    MeasurableSpace (LowerQuotient h F) := borel _
local instance sliceConvergenceLowerBorel {t : ℕ} {m : Fin 2 → ℕ}
    (h : ∑ i, (m i + 1) = t + 1) :
    BorelSpace (LowerQuotient h F) := ⟨rfl⟩

variable {t r : ℕ} {m : Fin 2 → ℕ}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Every actual standard quotient point has a torus times integral
representative; this is an existence argument, not a chosen section. -/
theorem exists_standard_torus_representative (q : LeftUnipotentQuotient t F) :
    ∃ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F),
      c ∈ integralOpen F t ∧ q = Quotient.mk _ (Iwasawa.torus
        (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c) := by
  induction q using Quotient.inductionOn with
  | h g =>
    obtain ⟨v, hv, lam, c, hc, rfl⟩ :=
      Iwasawa.exists_iwasawa (uniformizerUnit_isUniformizingElement F) g
    refine ⟨lam, c, (mem_integralOpen F c).mpr
      ((Conductor.mem_integralSubgroup _ t c).mp hc), ?_⟩
    rw [mul_assoc]
    exact leftQuotientMap_subgroup_mul _ ⟨v, hv⟩ _

/-- One threshold before all complementary dimensions gives a summable
majorant for the actual integrated raw norm and complex average. -/
theorem exists_summable_kernelNorm_majorant
    (ν : AdditiveHaarMeasure F) (h : ∑ i, (m i + 1) = t + 1)
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (a : Fin t) (ha : a.val = m 1) :
    ∃ C : ℝ, ∀ (u : ℝ), C < u →
      ∀ (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
        (j k : ℕ) (hr : r = t + (j + k + 1))
        (Wtest : (coefficientModel π lambda).toSubmodule),
      ∃ A : (Fin (t + 1) → ℤ) → ℝ,
        (∀ lam, 0 ≤ A lam) ∧
        Summable (fun lam => diagonalDensity F lam * A lam) ∧
        ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F),
          c ∈ integralOpen F t →
          let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
          let z := (lowerToStandard h F).symm (Quotient.mk _
            (Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
              (⟨⟩ : LocalFieldData F)) lam * c))
          let s0 : ℂ := ((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)
          quotientFiberIntegrable ν ellu f Wtest.val hr s0 z ∧
          ‖quotientKernel ν ellu f Wtest.val hr s0 z‖ ≤ A lam ∧
          ‖quotientNormProfile ν ellu f Wtest.val hr s0 z‖ ≤ A lam := by
  classical
  obtain ⟨B, hB, hbound⟩ :=
    exists_kernelNorm_torus_envelope ν h ψ π hπ lambda τ hτ ell a ha
  let q : ℝ := (⟨⟩ : LocalFieldData F).residueCardinality
  let D : ℝ := q ^ (2 * (t + 1) * (t + 1))
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  have hD : 1 ≤ D := one_le_pow₀ hq.le
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨C, _, hC⟩ := exists_geometric_twist_threshold (B := D * B) hq
  refine ⟨C, fun u hu f j k hr Wtest => ?_⟩
  obtain ⟨hu0, hratio⟩ := hC u hu
  obtain ⟨K, M, hK0, hK⟩ := hbound u f j k hr Wtest
  refine ⟨coneMajorant (Finset.Iic a.castSucc) K B q u M,
    coneMajorant_nonneg _ hK0 hB0 (zero_le_one.trans hq.le), ?_, ?_⟩
  · apply Summable.of_nonneg_of_le
      (fun lam => mul_nonneg (diagonalDensity_nonneg F lam)
        (coneMajorant_nonneg _ hK0 hB0 (zero_le_one.trans hq.le) lam)) _
      ((summable_cone_twist (M := M) (Finset.Iic a.castSucc) hq
        (mul_nonneg (zero_le_one.trans hD) hB0) hu0 hratio).mul_left K)
    intro lam
    unfold coneMajorant
    split_ifs with hc
    · calc
        _ ≤ D ^ torusSize lam * (K * B ^ torusSize lam *
            q ^ (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ))) :=
          mul_le_mul_of_nonneg_right (diagonalDensity_le F lam) (by positivity)
        _ = _ := by rw [mul_pow]; ring
    · simp
  · intro lam c hc
    dsimp only
    rw [lowerToStandard_symm_mk]
    have henv := hK lam c hc
    dsimp only at henv
    simp only [mul_assoc] at henv
    obtain ⟨hi, hn, hp0, hp, hs⟩ := henv
    change FiberIntegrable _ _ _ _ _ _ _ ∧
      ‖representativeKernel _ _ _ _ _ _ _‖ ≤ _ ∧
      ‖representativeNormProfile _ _ _ _ _ _ _‖ ≤ _
    refine ⟨hi, ?_⟩
    have hprofile : representativeNormProfile ν
        (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)) f Wtest.val hr
        (((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ))
        ((blockRotation h F)⁻¹ *
          (Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
            (⟨⟩ : LocalFieldData F)) lam * c)) ≤
          coneMajorant (Finset.Iic a.castSucc) K B q u M lam := by
      unfold coneMajorant
      split_ifs with hcone
      · simpa only [mul_assoc] using hp
      · have hz : representativeNormProfile ν
            (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)) f Wtest.val hr
            (((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ))
            ((blockRotation h F)⁻¹ *
              (Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
                (⟨⟩ : LocalFieldData F)) lam * c)) = 0 := by
          by_contra hne
          exact hcone (hs (by simpa only [mul_assoc] using hne))
        rw [hz]
    constructor
    · exact hn.trans hprofile
    · rw [Real.norm_eq_abs, abs_of_nonneg (by simpa only [mul_assoc] using hp0)]
      exact hprofile

/-- A measurable actual kernel and raw-norm profile with one summable torus
bound give genuine absolute input for the exact supplied quotient measure.
The fiber assertion is extended to every quotient point by Iwasawa coverage. -/
theorem kernelAbsoluteIntegrable_of_summable_torus_bound
    {j k : ℕ} {h : ∑ i, (m i + 1) = t + 1}
    {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
    {ψ : UnitaryAdditiveCharacter F}
    (ν : AdditiveHaarMeasure F)
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (hN : Measure.IsMulRightInvariant (unipotentHaar F t))
    (νN : Measure (LeftUnipotentQuotient t F))
    (hνN : standardCompatible F hN νN)
    (A : (Fin (t + 1) → ℤ) → ℝ)
    (hsum : Summable (fun lam => diagonalDensity F lam * A lam))
    (hbound : ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F),
      c ∈ integralOpen F t →
      let z := (lowerToStandard h F).symm (Quotient.mk _
        (Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
          (⟨⟩ : LocalFieldData F)) lam * c))
      quotientFiberIntegrable ν ell f Wtest.val hr s z ∧
      ‖quotientKernel ν ell f Wtest.val hr s z‖ ≤ A lam ∧
      ‖quotientNormProfile ν ell f Wtest.val hr s z‖ ≤ A lam) :
    KernelAbsoluteIntegrable ν ell f Wtest.val hr s νN ∧
      ∀ z, quotientFiberIntegrable ν ell f Wtest.val hr s z := by
  let := hN
  let E : LeftUnipotentQuotient t F → ℂ := fun q =>
    quotientKernel ν ell f Wtest.val hr s ((lowerToStandard h F).symm q)
  let P : LeftUnipotentQuotient t F → ℝ := fun q =>
    quotientNormProfile ν ell f Wtest.val hr s ((lowerToStandard h F).symm q)
  have hE : Measurable E :=
    (measurable_quotientKernel ν ell f π hπ lambda Wtest hr s).comp
      (canonicalLowerToStandardHomeomorph F h).symm.continuous.measurable
  have hP : Measurable P :=
    (measurable_quotientNormProfile ν ell f π hπ lambda Wtest hr s).comp
      (canonicalLowerToStandardHomeomorph F h).symm.continuous.measurable
  have hEi : Integrable E νN := by
    apply Langlands.AllField.RankinSelberg.QuotientTorusEnvelope.integrable_of_summable_torus_bound
      F (⟨⟩ : LocalFieldData F) t νN hνN
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
      (uniformizerUnit_isUniformizingElement F) E hE A _ hsum
    intro lam c hc
    exact (hbound lam c ((mem_integralOpen F c).mpr
      ((Conductor.mem_integralSubgroup _ t c).mp hc))).2.1
  have hPiC : Integrable (fun q => (P q : ℂ)) νN := by
    apply Langlands.AllField.RankinSelberg.QuotientTorusEnvelope.integrable_of_summable_torus_bound
      F (⟨⟩ : LocalFieldData F) t νN hνN
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
      (uniformizerUnit_isUniformizingElement F) _ (Complex.measurable_ofReal.comp hP)
      A _ hsum
    intro lam c hc
    change ‖(P (Quotient.mk _ (Iwasawa.torus
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c)) : ℂ)‖ ≤ _
    rw [Complex.norm_real]
    exact (hbound lam c ((mem_integralOpen F c).mpr
      ((Conductor.mem_integralSubgroup _ t c).mp hc))).2.2
  have hPi : Integrable P νN := by
    change Integrable (fun q => (P q : ℂ).re) νN
    exact hPiC.re
  have hfiber : ∀ z, quotientFiberIntegrable ν ell f Wtest.val hr s z := by
    intro z
    obtain ⟨lam, c, hc, heq⟩ :=
      exists_standard_torus_representative ((lowerToStandard h F) z)
    have hz : z = (lowerToStandard h F).symm (Quotient.mk _
        (Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
          (⟨⟩ : LocalFieldData F)) lam * c)) := by
      apply (lowerToStandard h F).injective
      simpa only [Equiv.apply_symm_apply] using heq
    rw [hz]
    exact (hbound lam c hc).1
  refine ⟨(kernelAbsoluteIntegrable_standard_iff ν ell f Wtest.val hr s νN).mpr
    ⟨hEi, hPi, Filter.Eventually.of_forall (fun q => hfiber _)⟩, hfiber⟩

/-- Restricting the supplied standard measure restricts all three actual
absolute-input conditions to the corresponding lower determinant slice. -/
theorem kernelAbsoluteIntegrable_restrict
    {j k : ℕ} {h : ∑ i, (m i + 1) = t + 1}
    {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
    {ψ : UnitaryAdditiveCharacter F}
    (ν : AdditiveHaarMeasure F)
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F))
    (hi : KernelAbsoluteIntegrable ν ell f Wtest hr s νN) (d : ℤ) :
    KernelAbsoluteIntegrable ν ell f Wtest hr s
      (νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t d)) := by
  rcases hi with ⟨hK, hP, hf⟩
  change Integrable _ _ ∧ Integrable _ _ ∧ _
  have hm : lowerMeasure F h
      (νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t d)) =
      (lowerMeasure F h νN).restrict
        (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d) :=
    (lowerMeasure_restrict F h νN d).symm
  rw [hm]
  exact ⟨hK.restrict, hP.restrict, ae_restrict_of_ae hf⟩

/-- One bound precedes the twist, every supplied compatible measure, both
rectangle dimensions and all tests. Convergence on each determinant slice
holds for every spectral parameter, independently of any epsilon equation. -/
def IsUniformSliceConvergence
    (ν : AdditiveHaarMeasure F) (h : ∑ i, (m i + 1) = t + 1)
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u →
    ∀ (hN : Measure.IsMulRightInvariant (unipotentHaar F t))
      (νN : Measure (LeftUnipotentQuotient t F)),
      standardCompatible F hN νN →
      ∀ (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
        (j k : ℕ) (hr : r = t + (j + k + 1))
        (Wtest : (coefficientModel π lambda).toSubmodule),
        let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
        (∀ s : ℂ, Measurable (quotientKernel ν ellu f Wtest.val hr s) ∧
          Measurable (quotientNormProfile ν ellu f Wtest.val hr s)) ∧
        (∀ (s : ℂ) z, quotientFiberIntegrable ν ellu f Wtest.val hr s z) ∧
        ∀ (s : ℂ) (d : ℤ), KernelAbsoluteIntegrable ν ellu f Wtest.val hr s
          (νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t d))

/-- The actual raw-norm envelope and quotient integration prove the uniform
slice convergence package for full Whittaker-type representations. -/
theorem exists_uniform_slice_convergence
    (ν : AdditiveHaarMeasure F) (h : ∑ i, (m i + 1) = t + 1)
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) :
    ∃ C : ℝ, IsUniformSliceConvergence ν h ψ π lambda τ ell C := by
  have hlt : m 1 < t := by
    have hh : m 0 + 1 + (m 1 + 1) = t + 1 := by
      simpa only [Fin.sum_univ_two] using h
    omega
  let a : Fin t := ⟨m 1, hlt⟩
  obtain ⟨C, hC⟩ :=
    exists_summable_kernelNorm_majorant ν h ψ π hπ lambda τ hτ ell a rfl
  refine ⟨C, fun u hu hN νN hνN f j k hr Wtest => ?_⟩
  dsimp only
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
  let s0 : ℂ := ((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)
  obtain ⟨A, _, hsum, hb⟩ := hC u hu f j k hr Wtest
  obtain ⟨hi, hf⟩ := kernelAbsoluteIntegrable_of_summable_torus_bound
    ν ellu f π hπ.1.1 lambda Wtest hr s0 hN νN hνN A hsum hb
  have hf0 (z : LowerQuotient h F) :
      quotientFiberIntegrable ν ellu f Wtest.val hr 0 z :=
    (quotientFiberIntegrable_spectral_iff ν ellu f Wtest.val hr s0 z).mp (hf z)
  refine ⟨fun s => ⟨measurable_quotientKernel ν ellu f π hπ.1.1 lambda Wtest hr s,
    measurable_quotientNormProfile ν ellu f π hπ.1.1 lambda Wtest hr s⟩,
    fun s z => (quotientFiberIntegrable_spectral_iff ν ellu f Wtest.val hr s z).mpr (hf0 z),
    fun s d => ?_⟩
  have hi0 := (kernelAbsoluteIntegrable_restrict_spectral_iff
    ν ellu f Wtest.val νN hr s0 d).mp
      (kernelAbsoluteIntegrable_restrict ν ellu f Wtest.val hr s0 νN hi d)
  exact (kernelAbsoluteIntegrable_restrict_spectral_iff
    ν ellu f Wtest.val νN hr s d).mpr hi0

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
