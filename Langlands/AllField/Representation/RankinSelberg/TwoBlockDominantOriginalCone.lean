import Langlands.Representation.RankinSelberg.TwoBlockDominantOriginalCone
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstEndpointBounds
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantSectionSupport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceMajorant
/-! # Original-torus opposite support for the actual dominant product -/

noncomputable section

open scoped BigOperators

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding IsBlockSumLastEntryBound IsBlockSumRectangularSupport IsLeviFirstInverseEndpointBound IsLeviFirstRectangularSupport IsLeviSecondEndpointBound IsLeviSecondRectangularSupport IsTorusBlockSupport append_mem_integralOpen blockSum_mem_integralOpen diagonalRightPermutation_mem_integralOpen dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation endpointBoundsTopology exists_blockSum_last_entry_bound exists_blockSum_rectangular_support exists_coefficient_blockSum_rootBounded exists_levi_first_inverse_endpoint_bound exists_levi_first_rectangular_support exists_levi_second_endpoint_bound exists_levi_second_rectangular_support exists_reindex_blockSum_last_entry_bound exists_reindex_blockSum_rectangular_support exists_rotated_torus_oppositeCone exists_torus_block_support firstEndpointLocalField firstEndpointTopology firstEndpointValuation instIsNonarchimedeanLocalFieldCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier_1 integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange iwasawa_principal_suffix_minor_bound measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange normalizedAbs_ratios_of_rootBounded originalConeTopology permutation_mem_integralOpen rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel twoBlockDominantBlockSupportLocalInstance1 unequalRankMatrix_last_entry_bound
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val unequalRankIwasawaSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement exists_rowSchwartz_order_lower_bound padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding blockRotation_inv_mul_torus determinantNorm_torus determinantNorm_torus_bounds diagonalDensity diagonalDensity_le diagonalDensity_nonneg exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_integrand_torus_majorant exists_rotated_section_growth exists_section_growth exists_standard_functional_growth exists_summable_integrand_majorant instBorelSpaceCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_4 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integrand_standard_mk isEntryBounded_torus normalizedAbs_uniformizer_zpow torusLevi torusLevi_embedding torusLevi_entryBounded torusLevi_inv_halfModulus_le torusLevi_rotated_twist
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockDominantSectionSupport hiding IsSectionTorusRootBounded exists_blockTensor_rootBounded exists_integral_blockTensor_rootBounded exists_section_torus_rootBounded sectionSupportLocalField sectionSupportTopology sectionSupportValuativeRel
open Langlands.AllField.RankinSelberg.TwoBlockDominantSectionSupport

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {t r j k : ℕ} {m : Fin 2 → ℕ}
variable (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- On the support of the actual coefficient times the actual scalar section,
all original first-block exponents are bounded above and all original
second-block exponents are bounded below. -/
def IsTorusBlockSupport
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (lambda : glFunctionals ψ r π) (Wtest : (coefficientModel π lambda).toSubmodule)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) (u : ℝ)
    (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)) (M : ℕ) : Prop :=
  ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F),
    c ∈ integralOpen F t →
    Wtest.val.val (matrix h hr (Iwasawa.torus
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c) x y) ≠ 0 →
    scalarSection (fun i => (ell i).val) f (Iwasawa.torus
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c) 1 ≠ 0 →
    (∀ a, lam ((succBlockShape m h).index 0 a) ≤ M) ∧
      (∀ a, -(M : ℤ) ≤ lam ((succBlockShape m h).index 1 a))

/-- Endpoint estimates and internal section-root support give one cutoff before
all original torus exponents, integral factors and rectangles. -/
theorem exists_torus_block_support
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsSmooth (τ i)) (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (u : ℝ) (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)) :
    ∃ M, IsTorusBlockSupport F h hr ψ π lambda Wtest τ ell u f M := by
  obtain ⟨B₀, _, hB₀⟩ := exists_levi_first_inverse_endpoint_bound F ψ h hr π hπ lambda Wtest
  obtain ⟨B₁, _, hB₁⟩ := exists_levi_second_endpoint_bound F ψ h hr π hπ lambda Wtest
  obtain ⟨L, hL⟩ := exists_section_torus_rootBounded F h ψ τ hτ ell u f
  have hq : (1 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  obtain ⟨E, hE⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop
    (max B₀ B₁)).exists
  refine ⟨E + (m 0 + m 1) * L, fun lam c x y hc hw hs => ?_⟩
  have hw' : Wtest.val.val (matrix h hr
      ((succBlockShape m h).leviEmbedding F (torusLevi F h lam) * c) x y) ≠ 0 := by
    simpa only [torusLevi_embedding] using hw
  have hzero := hB₀ (torusLevi F h lam) c x y hc hw'
  have hone := hB₁ (torusLevi F h lam) c x y hc hw'
  have hzpow : (⟨⟩ : LocalFieldData F).normalizedAbs
      (((torusLevi F h lam) 0)⁻¹ 0 0) =
        ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
          (lam ((succBlockShape m h).index 0 0)) := by
    change (⟨⟩ : LocalFieldData F).normalizedAbs
      ((Iwasawa.torus _ _)⁻¹.val 0 0) = _
    rw [Iwasawa.torus_inv_val, Matrix.diagonal_apply_eq, ← zpow_neg,
      normalizedAbs_uniformizer_zpow F, neg_neg]
  have hopow : (⟨⟩ : LocalFieldData F).normalizedAbs
      (torusLevi F h lam 1 (Fin.last (m 1)) (Fin.last (m 1))) =
        ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
          (-lam ((succBlockShape m h).index 1 (Fin.last (m 1)))) := by
    change (⟨⟩ : LocalFieldData F).normalizedAbs ((Iwasawa.torus _ _).val _ _) = _
    rw [Iwasawa.torus_val, Matrix.diagonal_apply_eq, normalizedAbs_uniformizer_zpow F]
  rw [hzpow] at hzero
  rw [hopow] at hone
  have he₀ : lam ((succBlockShape m h).index 0 0) ≤ E := by
    apply (zpow_le_zpow_iff_right₀ hq).mp
    rw [zpow_natCast]
    exact hzero.trans ((le_max_left _ _).trans hE.le)
  have he₁ : -(E : ℤ) ≤ lam ((succBlockShape m h).index 1 (Fin.last (m 1))) := by
    have he : -lam ((succBlockShape m h).index 1 (Fin.last (m 1))) ≤ E := by
      apply (zpow_le_zpow_iff_right₀ hq).mp
      rw [zpow_natCast]
      exact hone.trans ((le_max_right _ _).trans hE.le)
    omega
  have hroots := hL lam c hc hs
  constructor
  · intro a
    have hp := (hroots 0).le_of_le (Fin.zero_le a)
    push_cast
    push_cast at hp
    have hn : (0 : ℤ) ≤ m 1 * L := by positivity
    nlinarith
  · intro a
    have hp := (hroots 1).le_of_le (Fin.le_last a)
    push_cast
    push_cast at hp
    have hn : (0 : ℤ) ≤ m 0 * L := by positivity
    nlinarith

/-- At actual inverse-rotated torus representatives, simultaneous nonvanishing
of the ambient coefficient and scalar section forces one opposite cone. -/
theorem exists_rotated_torus_oppositeCone
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsSmooth (τ i)) (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (u : ℝ) (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
    (a : Fin t) (ha : a.val = m 1) :
    ∃ M : ℕ, ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F)
      (x : Matrix (Fin (m 0 + 1)) (Fin k) F)
      (y : Matrix (Fin j) (Fin (m 1 + 1)) F),
      c ∈ integralOpen F t →
      let g := (blockRotation h F)⁻¹ * Iwasawa.torus
        (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c
      Wtest.val.val (matrix h hr g x y) ≠ 0 →
      scalarSection (fun i => (ell i).val) f g 1 ≠ 0 →
      OppositeCone M (Finset.Iic a.castSucc) lam := by
  obtain ⟨M, hM⟩ := exists_torus_block_support F h hr ψ π hπ lambda Wtest τ hτ ell u f
  refine ⟨M, fun lam c x y hc hw hs => ?_⟩
  have he : (blockRotation h F)⁻¹ * Iwasawa.torus
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c =
      Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
        (rotatedExponents h lam) * ((blockRotation h F)⁻¹ * c) := by
    rw [blockRotation_inv_mul_torus, mul_assoc]
  rw [he] at hw hs
  obtain ⟨h₀, h₁⟩ := hM (rotatedExponents h lam) ((blockRotation h F)⁻¹ * c)
    x y (blockRotation_inv_mul_mem_integralOpen F h hc) hw hs
  exact oppositeCone_rotated_of_block_bounds h lam M a ha h₀ h₁

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
