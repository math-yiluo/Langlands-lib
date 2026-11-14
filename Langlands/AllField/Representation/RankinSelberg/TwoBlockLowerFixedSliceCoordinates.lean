import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceCoordinates
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceDensity
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
/-! # Rotated diagonal coordinates and the exact opposing twist -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding determinantNorm_torus determinantNorm_torus_bounds diagonalDensity diagonalDensity_le exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_section_growth exists_standard_functional_growth instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 isEntryBounded_torus normalizedAbs_uniformizer_zpow torusLevi torusLevi_embedding torusLevi_entryBounded torusLevi_inv_halfModulus_le torusLevi_rotated_twist
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

variable (F : Type uF) [Field F]

/-- Reassembling the extracted diagonal blocks gives the original torus. -/
theorem torusLevi_embedding [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (lam : Fin (t + 1) → ℤ) :
    (succBlockShape m h).leviEmbedding F (torusLevi F h lam) =
      Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
        lam := by
  apply Units.ext
  ext k l
  obtain ⟨⟨i, a⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective k
  obtain ⟨⟨j, b⟩, rfl⟩ := (succBlockShape m h).indexEquiv.surjective l
  change (succBlockShape m h).leviEmbedding F (torusLevi F h lam)
      ((succBlockShape m h).index i a) ((succBlockShape m h).index j b) = _
  by_cases hij : i = j
  · subst j
    rw [BlockShape.leviEmbedding_apply_same]
    change (Iwasawa.torus _ _) a b = (Iwasawa.torus _ lam)
      ((succBlockShape m h).index i a) ((succBlockShape m h).index i b)
    change (Matrix.diagonal _) a b = (Matrix.diagonal _)
      ((succBlockShape m h).index i a) ((succBlockShape m h).index i b)
    by_cases hab : a = b
    · subst b
      simp
    · simp [hab, ((succBlockShape m h).index i).injective.ne hab]
  · rw [BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hij]
    change 0 = (Matrix.diagonal _)
      ((succBlockShape m h).index i a) ((succBlockShape m h).index j b)
    have hne : (succBlockShape m h).index i a ≠ (succBlockShape m h).index j b := by
      intro he
      exact hij (congrArg Sigma.fst ((succBlockShape m h).indexEquiv.injective he))
    simp [hne]

/-- The determinant factors of the two opposing twists become precisely
`q` to minus the twist times the signed degree in standard coordinates. -/
theorem torusLevi_rotated_twist [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (lam : Fin (t + 1) → ℤ)
    (j : Fin t) (hj : j.val = m 1) (u : ℝ) :
    ((((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1)
        (torusLevi F h (rotatedExponents h lam) 0) : ℝ≥0) : ℝ) ^ (-u) *
      (((⟨⟩ : LocalFieldData F).determinantNorm (m 1 + 1)
        (torusLevi F h (rotatedExponents h lam) 1) : ℝ≥0) : ℝ) ^ u) =
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
        (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ)) := by
  change ((((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1)
      (Iwasawa.torus _ _) : ℝ≥0) : ℝ) ^ (-u) *
    (((⟨⟩ : LocalFieldData F).determinantNorm (m 1 + 1)
      (Iwasawa.torus _ _) : ℝ≥0) : ℝ) ^ u) = _
  rw [determinantNorm_torus F, determinantNorm_torus F,
    ← Real.rpow_intCast, ← Real.rpow_intCast]
  have hq : (0 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one)
  rw [← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_add hq,
    twistDegree_rotatedExponents h lam j hj]
  congr 1
  push_cast
  ring

end Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
