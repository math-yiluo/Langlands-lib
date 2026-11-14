import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstEndpointBounds
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEndpointBounds
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstRectangleSupport
/-! # First inverse-endpoint bound through actual reversed duality -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding IsBlockSumLastEntryBound IsBlockSumRectangularSupport IsLeviFirstInverseEndpointBound IsLeviFirstRectangularSupport IsLeviSecondEndpointBound IsLeviSecondRectangularSupport append_mem_integralOpen blockSum_mem_integralOpen diagonalRightPermutation_mem_integralOpen dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation endpointBoundsTopology exists_blockSum_last_entry_bound exists_blockSum_rectangular_support exists_coefficient_blockSum_rootBounded exists_levi_first_inverse_endpoint_bound exists_levi_first_rectangular_support exists_levi_second_endpoint_bound exists_levi_second_rectangular_support exists_reindex_blockSum_last_entry_bound exists_reindex_blockSum_rectangular_support firstEndpointLocalField firstEndpointTopology firstEndpointValuation instIsNonarchimedeanLocalFieldCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier_1 integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange iwasawa_principal_suffix_minor_bound measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange normalizedAbs_ratios_of_rootBounded permutation_mem_integralOpen rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel twoBlockDominantBlockSupportLocalInstance1 unequalRankMatrix_last_entry_bound
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val unequalRankIwasawaSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- The initial entry of the inverse first Levi block is uniformly bounded
on the support of the actual dominant coefficient. -/
def IsLeviFirstInverseEndpointBound
    (ψ : UnitaryAdditiveCharacter F)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ell : glFunctionals ψ r π) (W : (coefficientModel π ell).toSubmodule)
    (B : ℝ) : Prop :=
  1 ≤ B ∧ ∀ (b : (succBlockShape m h).Levi F)
    (c : GeneralLinear (t + 1) F)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F),
    c ∈ integralOpen F t →
    W.val.val (matrix h hr ((succBlockShape m h).leviEmbedding F b * c) x y) ≠ 0 →
    (⟨⟩ : LocalFieldData F).normalizedAbs ((b 0)⁻¹ 0 0) ≤ B

/-- Every smooth ambient coefficient has an actual first inverse-endpoint bound. -/
theorem exists_levi_first_inverse_endpoint_bound
    (ψ : UnitaryAdditiveCharacter F)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ B, IsLeviFirstInverseEndpointBound F ψ h hr π ell W B := by
  let WD := translatedFirstDualModelEquiv ψ π ell (rightWeyl hr) W
  obtain ⟨B, hB, hsupport⟩ :=
    exists_levi_second_endpoint_bound F (ψ.scale (-1)) (reverse_sum h)
      (by omega : r = t + (k + j + 1))
      (inverseTransposePullback π) (inverseTransposePullback_isSmooth π hπ)
      (firstDualFunctional ψ π ell) WD
  refine ⟨B, hB, fun b c x y hc hW => ?_⟩
  let cD := weylLong (t + 1) F * inverseTranspose (t + 1) F c
  have hcD : cD ∈ integralOpen F t :=
    (integralOpen F t).mul_mem (permutation_mem_integralOpen F t Fin.revPerm)
      (Langlands.AllField.RankinSelberg.TwoBlockDeformation.inverseTranspose_mem_integralOpen F hc)
  have hg :
      (succBlockShape (fun i => m i.rev) (reverse_sum h)).leviEmbedding F
          (reflectedLevi h b) * cD =
        weylLong (t + 1) F * inverseTranspose (t + 1) F
          ((succBlockShape m h).leviEmbedding F b * c) := by
    rw [← weyl_inverseTranspose_levi h b, map_mul]
    simp only [cD, mul_assoc]
    rw [← mul_assoc (weylLong (t + 1) F) (weylLong (t + 1) F),
      weylLong_mul_self, one_mul]
  have hD := hsupport (reflectedLevi h b) cD
    (signedReverseTranspose (m 1 + 1) j y) (signedReverseTranspose k (m 0 + 1) x) hcD
  have hWD :
      WD.val.val (matrix (reverse_sum h) (by omega : r = t + (k + j + 1))
        ((succBlockShape (fun i => m i.rev) (reverse_sum h)).leviEmbedding F
          (reflectedLevi h b) * cD)
        (signedReverseTranspose (m 1 + 1) j y)
        (signedReverseTranspose k (m 0 + 1) x)) ≠ 0 := by
    rw [hg]
    change W.val.val (weylLong (r + 1) F *
      inverseTranspose (r + 1) F (reversedMatrix h hr
        (weylLong (t + 1) F * inverseTranspose (t + 1) F
          ((succBlockShape m h).leviEmbedding F b * c))
        (signedReverseTranspose (m 1 + 1) j y)
        (signedReverseTranspose k (m 0 + 1) x))) ≠ 0
    have he := ((twoBlockDominantDualMatrix F t r j k m h hr).2
      (signedReverseTranspose (m 1 + 1) j y)
      (signedReverseTranspose k (m 0 + 1) x)).2
      ((succBlockShape m h).leviEmbedding F b * c)
    simpa only [he, signedReverseTranspose_apply, Fin.rev_rev, neg_neg] using hW
  have hresult := hD hWD
  change (⟨⟩ : LocalFieldData F).normalizedAbs
    ((weylLong (m 0 + 1) F * inverseTranspose (m 0 + 1) F (b 0) *
      weylLong (m 0 + 1) F) (Fin.last (m 0)) (Fin.last (m 0))) ≤ B at hresult
  simpa only [weylLong_conjugate_entry, inverseTranspose_entry, Fin.rev_last] using hresult

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
