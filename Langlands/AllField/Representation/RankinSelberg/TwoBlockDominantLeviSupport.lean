import Langlands.Representation.RankinSelberg.TwoBlockDominantLeviSupport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantBlockSupport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
/-! # Actual rectangle support at two-block Levi elements -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding IsBlockSumRectangularSupport IsLeviSecondRectangularSupport append_mem_integralOpen blockSum_mem_integralOpen diagonalRightPermutation_mem_integralOpen exists_blockSum_rectangular_support exists_coefficient_blockSum_rootBounded exists_levi_second_rectangular_support exists_reindex_blockSum_rectangular_support instTopologicalSpaceCarrier normalizedAbs_ratios_of_rootBounded permutation_mem_integralOpen twoBlockDominantBlockSupportLocalInstance1
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

/-- Unsigned permutation matrices belong to the actual integral subgroup. -/
theorem permutation_mem_integralOpen (n : ℕ) (s : Equiv.Perm (Fin (n + 1))) :
    permutation (n + 1) F s ∈ integralOpen F n := by
  rw [mem_integralOpen]
  constructor <;> intro i l
  · rw [permutation_entry]
    split <;> simp
  · rw [permutation_inv, permutation_entry]
    split <;> simp

variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- The right column-alignment permutation is integral. -/
theorem diagonalRightPermutation_mem_integralOpen
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1)) :
    diagonalRightPermutation (K := F) h hr ∈ integralOpen F r := by
  apply (integralOpen F r).mul_mem
  · exact permutation_mem_integralOpen F r Fin.revPerm
  · rw [blockWeyl_permutation]
    exact permutation_mem_integralOpen F r _

/-- The actual rank inclusion carries right integral factors to integral factors. -/
theorem append_mem_integralOpen (hr : r = t + (j + k + 1))
    {c : GeneralLinear (t + 1) F} (hc : c ∈ integralOpen F t) :
    append hr c ∈ integralOpen F r := by
  have hc' := (mem_integralOpen F c).mp hc
  rw [mem_integralOpen]
  constructor <;> intro i l
  · rw [append_entry]
    split_ifs
    · exact hc'.1 _ _
    · exact zero_mem _
    · exact one_mem _
    · exact zero_mem _
  · rw [← map_inv, append_entry]
    split_ifs
    · exact hc'.2 _ _
    · exact zero_mem _
    · exact one_mem _
    · exact zero_mem _

/-- Uniform block support transported only along equality of the actual ranks. -/
theorem exists_reindex_blockSum_rectangular_support
    (ψ : UnitaryAdditiveCharacter F) (n j k d r : ℕ)
    (H : n + (j + k + 1) + 1 + (d + 1) = r + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ C : Set (Matrix (Fin j) (Fin (n + 1)) F), IsCompact C ∧
      ∀ (g : GeneralLinear (n + 1) F)
        (Y : Matrix (Fin j) (Fin (n + 1)) F)
        (D : GeneralLinear (d + 1) F)
        (c : GeneralLinear (r + 1) F),
        c ∈ integralOpen F r →
        W.val.val (reindex (finCongr H) (blockSum (unequalRankMatrix j k g Y, D)) * c) ≠ 0 →
        Y ∈ C := by
  have hr : r = n + (j + k + 1) + 1 + d := by omega
  subst r
  exact exists_blockSum_rectangular_support F ψ n j k d π hπ ell W

/-- A single compact set bounds the actual reversed second rectangle times
its Levi block, uniformly in the first rectangle and the right integral factor. -/
def IsLeviSecondRectangularSupport
    (ψ : UnitaryAdditiveCharacter F)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ell : glFunctionals ψ r π) (W : (coefficientModel π ell).toSubmodule)
    (C : Set (Matrix (Fin j) (Fin (m 1 + 1)) F)) : Prop :=
  IsCompact C ∧ ∀ (b : (succBlockShape m h).Levi F)
    (c : GeneralLinear (t + 1) F)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F),
    c ∈ integralOpen F t →
    W.val.val (matrix h hr ((succBlockShape m h).leviEmbedding F b * c) x y) ≠ 0 →
    y.submatrix Fin.rev Fin.rev * (b 1).val ∈ C

/-- Actual compact second-rectangle support for every smooth ambient coefficient. -/
theorem exists_levi_second_rectangular_support
    (ψ : UnitaryAdditiveCharacter F)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ C, IsLeviSecondRectangularSupport F ψ h hr π ell W C := by
  obtain ⟨C, hC, hsupport⟩ :=
    exists_reindex_blockSum_rectangular_support F ψ (m 1) j 0 (k + m 0) r
      (diagonalBlocksRank h hr) π hπ ell W
  refine ⟨C, hC, fun b c x y hc hW => ?_⟩
  have he : matrix h hr ((succBlockShape m h).leviEmbedding F b * c) x y =
      reindex (finCongr (diagonalBlocksRank h hr))
        (blockSum (unequalRankMatrix j 0 (b 1)
          (y.submatrix Fin.rev Fin.rev * (b 1).val),
          trailingBlock (b 0) (x.submatrix Fin.rev Fin.rev))) *
        (diagonalRightPermutation h hr * append hr c) := by
    rw [← matrix_levi_diagonalBlocks h hr b x y]
    simp only [matrix, map_mul, mul_assoc, inv_mul_cancel_left]
  apply hsupport (b 1) _ (trailingBlock (b 0) (x.submatrix Fin.rev Fin.rev))
    (diagonalRightPermutation h hr * append hr c)
    ((integralOpen F r).mul_mem (diagonalRightPermutation_mem_integralOpen F h hr)
      (append_mem_integralOpen F hr hc))
  simpa only [← he] using hW

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
