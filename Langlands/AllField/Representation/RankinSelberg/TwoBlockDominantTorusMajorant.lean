import Langlands.Representation.RankinSelberg.TwoBlockDominantTorusMajorant
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantKernelRegularity
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantMatrixGrowth
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantOriginalCone
/-! # A uniform torus majorant for the actual dominant raw kernel -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable IsBlockSumLastEntryBound IsBlockSumRectangularSupport IsCoefficientRectangleGrowth IsLeviFirstInverseEndpointBound IsLeviFirstRectangularSupport IsLeviSecondEndpointBound IsLeviSecondRectangularSupport IsRawKernelTorusMajorant IsTorusBlockSupport IsTorusRectangleBoxSupport KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff append_isEntryBounded append_mem_integralOpen blockSum_mem_integralOpen box_mono box_mul box_neg_transpose box_of_reverse continuous_kernel determinantWeight_lowerBlockUnipotent_mul diagonalRightPermutation_mem_integralOpen dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation endpointBoundsTopology exists_blockSum_last_entry_bound exists_blockSum_rectangular_support exists_box_of_isCompact exists_coefficient_blockSum_rootBounded exists_coefficient_rectangle_growth_uniform exists_levi_first_inverse_endpoint_bound exists_levi_first_rectangular_support exists_levi_second_endpoint_bound exists_levi_second_rectangular_support exists_rawKernel_torus_majorant exists_reindex_blockSum_last_entry_bound exists_reindex_blockSum_rectangular_support exists_rotated_torus_oppositeCone exists_torus_block_support exists_torus_rectangle_box_support fiberIntegrable_lowerBlockUnipotent_mul_iff firstEndpointLocalField firstEndpointTopology firstEndpointValuation instIsNonarchimedeanLocalFieldCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier_1 integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange isEntryBounded_reflected iwasawa_principal_suffix_minor_bound kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_standard_iff kernelRegularityBorel kernelRegularityGLBorel kernelRegularityGLLocallyCompact kernelRegularityGLMeasurable kernelRegularityGLSecondCountable kernelRegularityLocalField kernelRegularityMatrixBorel kernelRegularityMatrixSecondCountable kernelRegularityMeasurable kernelRegularitySecondCountable kernelRegularityT2 kernelRegularityTopology kernelRegularityValuation kernel_covariance kernel_eq matrixGrowthTopology matrixGrowthValuation matrix_isEntryBounded measurableSet_rectangle_box measurable_quotientKernel measurable_quotientNormProfile measurable_representativeKernel measurable_representativeNormProfile measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange mem_box_iff_normalizedAbs mem_box_of_mul_mem_box normalizedAbs_ratios_of_rootBounded originalConeTopology outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField permutation_mem_integralOpen quotientFiberIntegrable quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientNormProfile quotientNormProfile_mk rawKernel rawKernel_covariance rawScalarValue rectangleBoxesBorel rectangleBoxesMeasurable rectangleBoxesTopology rectangleBoxesValuation rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_box rectangleMeasure_sigmaFinite rectangleUnipotent_isEntryBounded rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul standardCompatible standardCompatible_sigmaFinite torusMajorantTopology torusMajorantValuation twoBlockDominantBlockSupportLocalInstance1 unequalRankMatrix_last_entry_bound
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice quotientIwasawaIntegration rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val unequalRankIwasawaSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement exists_rowSchwartz_order_lower_bound padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
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
open scoped BigOperators

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- The ambient coefficient growth base can be chosen before the complementary
rectangle dimensions and all their coefficient-image tests. -/
theorem exists_coefficient_rectangle_growth_uniform
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (j k : ℕ) (hr : r = t + (j + k + 1)),
      IsCoefficientRectangleGrowth F h hr ψ π lambda B := by
  obtain ⟨B, hB, hcoeff⟩ := exists_coefficient_growth F ψ π hπ lambda
  refine ⟨B * B, one_le_mul_of_one_le_of_one_le hB hB, fun j k hr Wtest => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hcoeff Wtest
  obtain ⟨N, hN⟩ :=
    exists_torus_rectangle_box_support F ψ h hr π hπ.1.1 lambda Wtest
  refine ⟨C * B ^ N, by positivity, fun lam c x y hc => ?_⟩
  by_cases hw : Wtest.val.val (matrix h hr (Iwasawa.torus
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c) x y) = 0
  · rw [hw, norm_zero]
    positivity
  obtain ⟨hx, hy⟩ := hN lam c x y hc hw
  have htorus := isEntryBounded_torus F (uniformizerUnit_isUniformizingElement F)
    lam (torusSize lam) (torusSize_bounds lam)
  have hc' : IsEntryBounded
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) 0 c := by
    have hi := (mem_integralOpen F c).mp hc
    intro i l
    simpa only [pow_zero, one_mul] using And.intro (hi.1 i l) (hi.2 i l)
  have hg := htorus.mul hc'
  rw [add_zero] at hg
  have hb := hC _ _ (matrix_isEntryBounded F h hr hg hx hy)
  calc
    _ ≤ C * B ^ (N + torusSize lam + torusSize lam) := hb
    _ = _ := by simp only [pow_add, mul_pow]; ring

/-- One growth base precedes every real twist, section, complementary rectangle
dimension and coefficient-image test. Nonzero raw values lie in both explicit
rectangle boxes and one opposing cone. -/
def IsRawKernelTorusMajorant
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (a : Fin t) (B : ℝ) : Prop :=
  ∀ (u : ℝ) (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
    (j k : ℕ) (hr : r = t + (j + k + 1))
    (Wtest : (coefficientModel π lambda).toSubmodule),
    ∃ (C : ℝ) (N M : ℕ), 0 ≤ C ∧
      ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F)
        (x : Matrix (Fin (m 0 + 1)) (Fin k) F)
        (y : Matrix (Fin j) (Fin (m 1 + 1)) F),
        c ∈ integralOpen F t →
        let g := (blockRotation h F)⁻¹ * Iwasawa.torus
          (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c
        let K := rawKernel
          (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i))
          f Wtest.val hr g x y
        ‖K‖ ≤ C * B ^ torusSize lam *
          ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
            (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ)) ∧
        (K ≠ 0 → OppositeCone M (Finset.Iic a.castSucc) lam ∧
          x ∈ box F (m 0 + 1) k (N + torusSize lam) ∧
          y ∈ box F j (m 1 + 1) (N + torusSize lam))

/-- The actual raw product has a uniform geometric bound and simultaneous
cone and rectangle support, with no integrability assumption. -/
theorem exists_rawKernel_torus_majorant
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (a : Fin t) (ha : a.val = m 1) :
    ∃ B : ℝ, 1 ≤ B ∧ IsRawKernelTorusMajorant F h ψ π lambda τ ell a B := by
  obtain ⟨Bw, hBw, hcoeff⟩ := exists_coefficient_rectangle_growth_uniform F h ψ π hπ lambda
  obtain ⟨Bs, hBs, hsection⟩ := exists_rotated_section_growth F h ψ τ hτ ell a ha
  refine ⟨Bw * Bs, one_le_mul_of_one_le_of_one_le hBw hBs,
    fun u f j k hr Wtest => ?_⟩
  obtain ⟨Cw, hCw0, hCw⟩ := hcoeff j k hr Wtest
  obtain ⟨Cs, hCs0, hCs⟩ := hsection u f
  obtain ⟨N, hN⟩ := exists_torus_rectangle_box_support F ψ h hr π hπ.1.1 lambda Wtest
  obtain ⟨M, hM⟩ := exists_rotated_torus_oppositeCone F h hr ψ π hπ.1.1
    lambda Wtest τ (fun i => (hτ i).1.1) ell u f a ha
  refine ⟨Cw * Cs, N, M, mul_nonneg hCw0 hCs0, fun lam c x y hc => ?_⟩
  dsimp only
  let g := (blockRotation h F)⁻¹ * Iwasawa.torus
    (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c
  have he : g = Iwasawa.torus
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
      (rotatedExponents h lam) * ((blockRotation h F)⁻¹ * c) := by
    dsimp only [g]
    rw [blockRotation_inv_mul_torus, mul_assoc]
  have hc' := blockRotation_inv_mul_mem_integralOpen F h hc
  have hw := hCw (rotatedExponents h lam) ((blockRotation h F)⁻¹ * c) x y hc'
  rw [← he, torusSize_rotatedExponents] at hw
  constructor
  · change ‖scalarSection _ f g 1 * Wtest.val.val (matrix h hr g x y)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ (Cs * Bs ^ torusSize lam *
          ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
            (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ))) *
          (Cw * Bw ^ torusSize lam) :=
        mul_le_mul (hCs lam c hc) hw (norm_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  · intro hne
    change scalarSection _ f g 1 * Wtest.val.val (matrix h hr g x y) ≠ 0 at hne
    obtain ⟨hsne, hwne⟩ := mul_ne_zero_iff.mp hne
    have hboxes := hN (rotatedExponents h lam) ((blockRotation h F)⁻¹ * c)
      x y hc' (by simpa only [← he] using hwne)
    rw [torusSize_rotatedExponents] at hboxes
    exact ⟨hM lam c x y hc hwne hsne, hboxes⟩

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
