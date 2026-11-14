import Langlands.Representation.RankinSelberg.TwoBlockDominantEndpointBounds
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantLeviSupport
/-! # Endpoint bounds in a leading unequal-rank block -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding IsBlockSumLastEntryBound IsBlockSumRectangularSupport IsLeviSecondEndpointBound IsLeviSecondRectangularSupport append_mem_integralOpen blockSum_mem_integralOpen diagonalRightPermutation_mem_integralOpen endpointBoundsTopology exists_blockSum_last_entry_bound exists_blockSum_rectangular_support exists_coefficient_blockSum_rootBounded exists_levi_second_endpoint_bound exists_levi_second_rectangular_support exists_reindex_blockSum_last_entry_bound exists_reindex_blockSum_rectangular_support instTopologicalSpaceCarrier iwasawa_principal_suffix_minor_bound normalizedAbs_ratios_of_rootBounded permutation_mem_integralOpen twoBlockDominantBlockSupportLocalInstance1 unequalRankMatrix_last_entry_bound
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val unequalRankIwasawaSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open scoped BigOperators
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_section_growth exists_standard_functional_growth instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 isEntryBounded_torus normalizedAbs_uniformizer_zpow
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice

universe uF uV

section Algebra

variable {K : Type uF} [Field K]

private theorem suffix_minor_mul {m : ℕ}
    (t : Fin m) (U A : Matrix (Fin m) (Fin m) K)
    (hU : U.IsUpperTriangular) (c : {i : Fin m // t ≤ i} → Fin m) :
    Matrix.det ((U * A).submatrix Subtype.val c) =
      (∏ i : {i : Fin m // t ≤ i}, U i i) *
        Matrix.det (A.submatrix Subtype.val c) := by
  classical
  have hm : (U * A).submatrix Subtype.val c =
      (U.submatrix Subtype.val Subtype.val :
        Matrix {i : Fin m // t ≤ i} {i : Fin m // t ≤ i} K) *
        A.submatrix Subtype.val c := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    apply Finset.sum_congr_set {q : Fin m | t ≤ q}
    · intro q hq
      rfl
    · intro q hq
      rw [hU (lt_of_lt_of_le (lt_of_not_ge hq) i.property), zero_mul]
  have hsub : (U.submatrix Subtype.val Subtype.val :
      Matrix {i : Fin m // t ≤ i} {i : Fin m // t ≤ i} K).IsUpperTriangular := by
    intro i j hij
    exact hU hij
  rw [hm, Matrix.det_mul, Matrix.det_of_isUpperTriangular hsub]
  rfl

private theorem det_mem_subring {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Subring K) (A : Matrix ι ι K) (hA : ∀ i j, A i j ∈ O) :
    A.det ∈ O := by
  let B : Matrix ι ι O := fun i j => ⟨A i j, hA i j⟩
  have he : (B.map O.subtype) = A := rfl
  rw [← he]
  change (O.subtype.mapMatrix B).det ∈ O
  rw [← O.subtype.map_det]
  exact (B.det).property

end Algebra

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- A principal suffix minor is bounded by the Iwasawa diagonal on that suffix. -/
theorem iwasawa_principal_suffix_minor_bound (r : ℕ)
    (u : GeneralLinear (r + 1) F)
    (a : Fin (r + 1) → Fˣ) (κ : GeneralLinear (r + 1) F)
    (hu : u ∈ upperUnipotent (r + 1) F)
    (hκ : κ ∈ integralOpen F r) (t : Fin (r + 1)) :
    (⟨⟩ : LocalFieldData F).normalizedAbs
      (Matrix.det ((u * Iwasawa.diagonalUnits a * κ).val.submatrix
        (Subtype.val : {i // t ≤ i} → _) Subtype.val)) ≤
      ∏ i : {i : Fin (r + 1) // t ≤ i},
        (⟨⟩ : LocalFieldData F).normalizedAbs (a i : F) := by
  classical
  have htri : (u * Iwasawa.diagonalUnits a).val.IsUpperTriangular := by
    intro i j hij
    change (u.val * (Iwasawa.diagonalUnits a).val) i j = 0
    rw [Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, hu.1 hij, zero_mul]
  have hdiag (i : Fin (r + 1)) :
      (u * Iwasawa.diagonalUnits a) i i = (a i : F) := by
    change (u.val * (Iwasawa.diagonalUnits a).val) i i = _
    rw [Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, hu.2 i, one_mul]
  have hdet : (κ.val.submatrix
      (Subtype.val : {i : Fin (r + 1) // t ≤ i} → _) Subtype.val).det ∈
      (⟨⟩ : LocalFieldData F).Integers :=
    det_mem_subring _ _ fun i l => ((mem_integralOpen F κ).mp hκ).1 i l
  have hle := ((⟨⟩ : LocalFieldData F).normalizedAbs_le_one_iff_mem_integers _).mpr hdet
  change (⟨⟩ : LocalFieldData F).normalizedAbs
    (Matrix.det (((u * Iwasawa.diagonalUnits a).val * κ.val).submatrix
      (Subtype.val : {i // t ≤ i} → _) Subtype.val)) ≤ _
  rw [suffix_minor_mul t _ _ htri Subtype.val]
  simp_rw [hdiag]
  rw [(⟨⟩ : LocalFieldData F).normalizedAbs_mul, normalizedAbs_prod F]
  exact (mul_le_mul_of_nonneg_left hle
    (Finset.prod_nonneg fun i _ => (⟨⟩ : LocalFieldData F).normalizedAbs_nonneg _)).trans_eq
      (mul_one _)

/-- A bounded adjacent Iwasawa ratio and the terminal identity row bound the
last entry of the original leading group block. -/
theorem unequalRankMatrix_last_entry_bound (n j k : ℕ)
    (g : GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F)
    (u : GeneralLinear (n + (j + k + 1) + 1) F)
    (a : Fin (n + (j + k + 1) + 1) → Fˣ)
    (κ : GeneralLinear (n + (j + k + 1) + 1) F)
    (hu : u ∈ upperUnipotent (n + (j + k + 1) + 1) F)
    (hκ : κ ∈ integralOpen F (n + (j + k + 1)))
    (he : unequalRankMatrix j k g x = u * Iwasawa.diagonalUnits a * κ)
    (B : ℝ) (hB : 1 ≤ B)
    (hroot : ∀ i : Fin (n + (j + k + 1)),
      (⟨⟩ : LocalFieldData F).normalizedAbs
        ((a i.castSucc / a i.succ : Fˣ) : F) ≤ B) :
    (⟨⟩ : LocalFieldData F).normalizedAbs (g (Fin.last n) (Fin.last n)) ≤
      (B ^ (n + (j + k + 1))) ^ (n + (j + k + 1) + 1) := by
  classical
  have hrow (b : Fin (n + (j + k + 1) + 1)) :
      unequalRankMatrix j k g x (Fin.last (n + (j + k + 1))) b =
        if Fin.last (n + (j + k + 1)) = b then 1 else 0 := by
    rw [unequalRankMatrix_val]
    simp [appendIdentity_entry, rectangularEntries, Fin.val_last,
      show ¬n + (j + k + 1) < n + 1 by omega,
      show ¬n + (j + k + 1) < n + 1 + j by omega]
  have hlast := diagonal_abs_last F (⟨⟩ : LocalFieldData F)
    (n + (j + k + 1)) _ u a κ hrow hu
    ((Conductor.mem_integralSubgroup _ _ κ).mpr ((mem_integralOpen F κ).mp hκ)) he
  have hdiag := diagonal_abs_bound F (⟨⟩ : LocalFieldData F)
    (n + (j + k + 1)) a B hB hlast hroot
  let t : Fin (n + (j + k + 1) + 1) := ⟨n, by omega⟩
  let S := {i : Fin (n + (j + k + 1) + 1) // t ≤ i}
  have hminor := iwasawa_principal_suffix_minor_bound F
    (n + (j + k + 1)) u a κ hu hκ t
  rw [← he, unequalRankMatrix_last_entry_minor] at hminor
  have hprod :
      (∏ i : S, (⟨⟩ : LocalFieldData F).normalizedAbs (a i : F)) ≤
        (B ^ (n + (j + k + 1))) ^ Fintype.card S := by
    calc
      _ ≤ ∏ _i : S, B ^ (n + (j + k + 1)) :=
        Finset.prod_le_prod₀ (fun i _ => (⟨⟩ : LocalFieldData F).normalizedAbs_nonneg _)
          (fun i _ => hdiag i)
      _ = _ := by simp
  have hcard : Fintype.card S ≤ n + (j + k + 1) + 1 :=
    (Fintype.card_le_of_injective (Subtype.val : S → _) Subtype.val_injective).trans_eq
      (Fintype.card_fin _)
  exact hminor.trans (hprod.trans
    (pow_le_pow_right₀ (one_le_pow₀ hB) hcard))

/-- An endpoint entry bound uniform in the rectangle, the other invertible
diagonal block and the right integral factor. -/
def IsBlockSumLastEntryBound (ψ : UnitaryAdditiveCharacter F)
    (n j k d : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ
      (GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F) V)
    (ell : glFunctionals ψ (n + (j + k + 1) + 1 + d) π)
    (W : (coefficientModel π ell).toSubmodule) (B : ℝ) : Prop :=
  1 ≤ B ∧ ∀ (g : GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F)
    (D : GeneralLinear (d + 1) F)
    (c : GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F),
    c ∈ integralOpen F (n + (j + k + 1) + 1 + d) →
    W.val.val (blockSum (unequalRankMatrix j k g x, D) * c) ≠ 0 →
    (⟨⟩ : LocalFieldData F).normalizedAbs (g (Fin.last n) (Fin.last n)) ≤ B

/-- A smooth ambient coefficient uniformly bounds the leading endpoint entry. -/
theorem exists_blockSum_last_entry_bound (ψ : UnitaryAdditiveCharacter F)
    (n j k d : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ
      (GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ (n + (j + k + 1) + 1 + d) π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ B, IsBlockSumLastEntryBound F ψ n j k d π ell W B := by
  obtain ⟨L, hL⟩ := exists_coefficient_blockSum_rootBounded F ψ π hπ ell W
  have hq : (1 : ℝ) ≤ (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one.le
  refine ⟨((((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ L) ^
    (n + (j + k + 1))) ^ (n + (j + k + 1) + 1),
    one_le_pow₀ (one_le_pow₀ (one_le_pow₀ hq)),
    fun g x D c hc hW => ?_⟩
  obtain ⟨uA, uB, lam, mu, kA, kB, huA, huB, hkA, hkB, heA, heB, hrA, hrB⟩ :=
    hL (unequalRankMatrix j k g x) D c hc hW
  exact unequalRankMatrix_last_entry_bound F n j k g x uA
    (fun i => Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F) ^ lam i)
    kA huA hkA heA _ (one_le_pow₀ hq)
    (normalizedAbs_ratios_of_rootBounded F hrA)

theorem exists_reindex_blockSum_last_entry_bound
    (ψ : UnitaryAdditiveCharacter F) (n j k d r : ℕ)
    (H : n + (j + k + 1) + 1 + (d + 1) = r + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (g : GeneralLinear (n + 1) F)
        (Y : Matrix (Fin j) (Fin (n + 1)) F)
        (D : GeneralLinear (d + 1) F)
        (c : GeneralLinear (r + 1) F),
        c ∈ integralOpen F r →
        W.val.val (reindex (finCongr H) (blockSum (unequalRankMatrix j k g Y, D)) * c) ≠ 0 →
        (⟨⟩ : LocalFieldData F).normalizedAbs (g (Fin.last n) (Fin.last n)) ≤ B := by
  have hr : r = n + (j + k + 1) + 1 + d := by omega
  subst r
  exact exists_blockSum_last_entry_bound F ψ n j k d π hπ ell W

variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- A bound for the actual second Levi block's terminal diagonal entry whenever
the coefficient at the actual dominant matrix is nonzero. -/
def IsLeviSecondEndpointBound
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
    (⟨⟩ : LocalFieldData F).normalizedAbs
      (b 1 (Fin.last (m 1)) (Fin.last (m 1))) ≤ B

/-- The actual second endpoint bound holds for every smooth ambient coefficient. -/
theorem exists_levi_second_endpoint_bound
    (ψ : UnitaryAdditiveCharacter F)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ B, IsLeviSecondEndpointBound F ψ h hr π ell W B := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_reindex_blockSum_last_entry_bound F ψ (m 1) j 0 (k + m 0) r
      (diagonalBlocksRank h hr) π hπ ell W
  refine ⟨B, hB, fun b c x y hc hW => ?_⟩
  have he : matrix h hr ((succBlockShape m h).leviEmbedding F b * c) x y =
      reindex (finCongr (diagonalBlocksRank h hr))
        (blockSum (unequalRankMatrix j 0 (b 1)
          (y.submatrix Fin.rev Fin.rev * (b 1).val),
          trailingBlock (b 0) (x.submatrix Fin.rev Fin.rev))) *
        (diagonalRightPermutation h hr * append hr c) := by
    rw [← matrix_levi_diagonalBlocks h hr b x y]
    simp only [matrix, map_mul, mul_assoc, inv_mul_cancel_left]
  apply hbound (b 1) (y.submatrix Fin.rev Fin.rev * (b 1).val)
    (trailingBlock (b 0) (x.submatrix Fin.rev Fin.rev))
    (diagonalRightPermutation h hr * append hr c)
    ((integralOpen F r).mul_mem (diagonalRightPermutation_mem_integralOpen F h hr)
      (append_mem_integralOpen F hr hc))
  simpa only [← he] using hW

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
