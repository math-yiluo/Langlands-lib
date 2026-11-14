import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstRectangleSupport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDualRectangles
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantLeviSupport
/-! # Compact first-rectangle support through actual reversed duality -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding IsBlockSumRectangularSupport IsLeviFirstRectangularSupport IsLeviSecondRectangularSupport append_mem_integralOpen blockSum_mem_integralOpen diagonalRightPermutation_mem_integralOpen dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation exists_blockSum_rectangular_support exists_coefficient_blockSum_rootBounded exists_levi_first_rectangular_support exists_levi_second_rectangular_support exists_reindex_blockSum_rectangular_support instIsNonarchimedeanLocalFieldCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier_1 integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange normalizedAbs_ratios_of_rootBounded permutation_mem_integralOpen rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel twoBlockDominantBlockSupportLocalInstance1
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

section Algebra


end Algebra

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- One compact set controls the first rectangle in reflected dual coordinates. -/
def IsLeviFirstRectangularSupport
    (ψ : UnitaryAdditiveCharacter F)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ell : glFunctionals ψ r π) (W : (coefficientModel π ell).toSubmodule)
    (C : Set (Matrix (Fin k) (Fin (m 0 + 1)) F)) : Prop :=
  IsCompact C ∧ ∀ (b : (succBlockShape m h).Levi F)
    (c : GeneralLinear (t + 1) F)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F),
    c ∈ integralOpen F t →
    W.val.val (matrix h hr ((succBlockShape m h).leviEmbedding F b * c) x y) ≠ 0 →
    (-x.transpose) *
      (weylLong (m 0 + 1) F * inverseTranspose (m 0 + 1) F (b 0) *
        weylLong (m 0 + 1) F).val ∈ C

/-- Actual compact first-rectangle support for every smooth ambient coefficient. -/
theorem exists_levi_first_rectangular_support
    (ψ : UnitaryAdditiveCharacter F)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ C, IsLeviFirstRectangularSupport F ψ h hr π ell W C := by
  let WD := translatedFirstDualModelEquiv ψ π ell (rightWeyl hr) W
  obtain ⟨C, hC, hsupport⟩ :=
    exists_levi_second_rectangular_support F (ψ.scale (-1)) (reverse_sum h)
      (by omega : r = t + (k + j + 1))
      (inverseTransposePullback π) (inverseTransposePullback_isSmooth π hπ)
      (firstDualFunctional ψ π ell) WD
  refine ⟨C, hC, fun b c x y hc hW => ?_⟩
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
  have hcoord :
      (signedReverseTranspose k (m 0 + 1) x).submatrix Fin.rev Fin.rev = -x.transpose := by
    ext i l
    simp only [Matrix.submatrix_apply, signedReverseTranspose_apply, Fin.rev_rev,
      Matrix.neg_apply, Matrix.transpose_apply]
  have hresult := hD hWD
  change (signedReverseTranspose k (m 0 + 1) x).submatrix Fin.rev Fin.rev *
    (weylLong (m 0 + 1) F * inverseTranspose (m 0 + 1) F (b 0) *
      weylLong (m 0 + 1) F).val ∈ C at hresult
  rw [hcoord] at hresult
  exact hresult

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
