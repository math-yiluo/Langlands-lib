import Langlands.Representation.RankinSelberg.TwoBlockDominantNormEnvelope
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantSliceSpectral
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantTorusMajorant
/-! # Integrable rectangle fibers and their actual raw-norm envelope -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable IsBlockSumLastEntryBound IsBlockSumRectangularSupport IsCoefficientRectangleGrowth IsKernelNormTorusEnvelope IsLeviFirstInverseEndpointBound IsLeviFirstRectangularSupport IsLeviSecondEndpointBound IsLeviSecondRectangularSupport IsRawKernelTorusMajorant IsTorusBlockSupport IsTorusRectangleBoxSupport KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff ae_quotientFiberIntegrable_spectral_iff append_isEntryBounded append_mem_integralOpen blockSum_mem_integralOpen box_mono box_mul box_neg_transpose box_of_reverse continuous_kernel determinantWeight_lowerBlockUnipotent_mul diagonalRightPermutation_mem_integralOpen dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation endpointBoundsTopology exists_blockSum_last_entry_bound exists_blockSum_rectangular_support exists_box_of_isCompact exists_coefficient_blockSum_rootBounded exists_coefficient_rectangle_growth_uniform exists_kernelNorm_torus_envelope exists_levi_first_inverse_endpoint_bound exists_levi_first_rectangular_support exists_levi_second_endpoint_bound exists_levi_second_rectangular_support exists_rawKernel_torus_majorant exists_reindex_blockSum_last_entry_bound exists_reindex_blockSum_rectangular_support exists_rotated_torus_oppositeCone exists_torus_block_support exists_torus_rectangle_box_support fiberIntegrable_lowerBlockUnipotent_mul_iff fiberIntegrable_spectral_iff fiber_integrable_normProfile_le_of_box firstEndpointLocalField firstEndpointTopology firstEndpointValuation instIsNonarchimedeanLocalFieldCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier_1 integrableOn_quotientKernel_spectral_iff integrableOn_quotientNormProfile_spectral_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange isEntryBounded_reflected iwasawa_principal_suffix_minor_bound kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_restrict_spectral_iff kernelAbsoluteIntegrable_standard_iff kernelRegularityBorel kernelRegularityGLBorel kernelRegularityGLLocallyCompact kernelRegularityGLMeasurable kernelRegularityGLSecondCountable kernelRegularityLocalField kernelRegularityMatrixBorel kernelRegularityMatrixSecondCountable kernelRegularityMeasurable kernelRegularitySecondCountable kernelRegularityT2 kernelRegularityTopology kernelRegularityValuation kernelSliceCoefficient kernel_covariance kernel_eq kernel_referenceParameter kernel_spectral matrixGrowthTopology matrixGrowthValuation matrix_isEntryBounded measurableSet_rectangle_box measurable_quotientKernel measurable_quotientNormProfile measurable_representativeKernel measurable_representativeNormProfile measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange mem_box_iff_normalizedAbs mem_box_of_mul_mem_box normEnvelopeBorel normEnvelopeLocalField normEnvelopeMatrixBorel normEnvelopeMatrixSecondCountable normEnvelopeMeasurable normEnvelopeSecondCountable normEnvelopeTopology normEnvelopeValuation normalizedAbs_ratios_of_rootBounded originalConeTopology outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField permutation_mem_integralOpen quotientFiberIntegrable quotientFiberIntegrable_spectral_iff quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_spectral quotientKernel_spectral_onSlice quotientNormProfile quotientNormProfile_mk quotientNormProfile_spectral quotientNormProfile_spectral_onSlice rawKernel rawKernel_covariance rawScalarValue rectangleBoxesBorel rectangleBoxesMeasurable rectangleBoxesTopology rectangleBoxesValuation rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_box rectangleMeasure_box_ne_top rectangleMeasure_real_box rectangleMeasure_real_box_le rectangleMeasure_sigmaFinite rectangleUnipotent_isEntryBounded rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_spectral representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul representativeNormProfile_spectral setIntegral_quotientKernel_spectral sliceSpectralMeasurable sliceSpectralTopology standardCompatible standardCompatible_sigmaFinite torusMajorantTopology torusMajorantValuation twoBlockDominantBlockSupportLocalInstance1 unequalRankMatrix_last_entry_bound
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

local instance normEnvelopeSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance normEnvelopeMeasurable : MeasurableSpace F := borel _
local instance normEnvelopeBorel : BorelSpace F := ⟨rfl⟩
local instance normEnvelopeMatrixBorel (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F))
local instance normEnvelopeMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F))

variable {t r j k : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable {ψ : UnitaryAdditiveCharacter F}

/-- The reference parameter removes the entire determinant weight. -/
theorem kernel_referenceParameter
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)
    (hr : r = t + (j + k + 1)) (g : GeneralLinear (t + 1) F)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F) :
    kernel ell f Wtest hr (((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)) g x y =
      rawKernel ell f Wtest hr g x y := by
  unfold kernel
  rw [show (((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)) -
      ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ) = 0 by ring]
  simp [determinantWeight]

/-- Each simultaneous rectangle box has finite supplied Haar volume. -/
theorem rectangleMeasure_box_ne_top (ν : AdditiveHaarMeasure F)
    (m : Fin 2 → ℕ) (j k e : ℕ) :
    rectangleMeasure F m j k ν
      ((box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) ≠ ∞ := by
  rw [rectangleMeasure_box]
  exact ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (⟨⟩ : LocalFieldData F).isCompact_integers.measure_ne_top)
    (ENNReal.pow_ne_top (ENNReal.pow_ne_top (by simp)))

/-- Domination by a constant on the actual finite box proves both genuine
fiber integrability and a bound for the integral of the raw norm. -/
theorem fiber_integrable_normProfile_le_of_box
    (ν : AdditiveHaarMeasure F)
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)
    (hr : r = t + (j + k + 1)) (s : ℂ) (g : GeneralLinear (t + 1) F)
    (e : ℕ) (A : ℝ)
    (hmeas : AEStronglyMeasurable
      (fun z : Rectangles m j k F => kernel ell f Wtest hr s g z.1 z.2)
      (rectangleMeasure F m j k ν))
    (hbound : ∀ z : Rectangles m j k F,
      ‖kernel ell f Wtest hr s g z.1 z.2‖ ≤ A)
    (hsupport : ∀ z : Rectangles m j k F,
      kernel ell f Wtest hr s g z.1 z.2 ≠ 0 →
        z ∈ (box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) :
    FiberIntegrable ν ell f Wtest hr s g ∧
      ‖representativeKernel ν ell f Wtest hr s g‖ ≤
        representativeNormProfile ν ell f Wtest hr s g ∧
      0 ≤ representativeNormProfile ν ell f Wtest hr s g ∧
      representativeNormProfile ν ell f Wtest hr s g ≤
        (rectangleMeasure F m j k ν).real
          ((box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) * A := by
  classical
  let S := (box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)
  have hS : MeasurableSet S := measurableSet_rectangle_box F m j k e
  have hI : Integrable (S.indicator (fun _ : Rectangles m j k F => A))
      (rectangleMeasure F m j k ν) :=
    (integrable_indicator_iff hS).mpr
      (integrableOn_const (C := A) (rectangleMeasure_box_ne_top ν m j k e))
  have hdom : ∀ z : Rectangles m j k F,
      ‖kernel ell f Wtest hr s g z.1 z.2‖ ≤ S.indicator (fun _ => A) z := by
    intro z
    by_cases hz : z ∈ S
    · simpa only [Set.indicator_of_mem hz] using hbound z
    · have hzero : kernel ell f Wtest hr s g z.1 z.2 = 0 := by
        by_contra hne
        exact hz (hsupport z hne)
      simp only [Set.indicator_of_notMem hz, hzero, norm_zero, le_refl]
  have hint := hI.mono' hmeas (Filter.Eventually.of_forall hdom)
  refine ⟨hint, norm_integral_le_integral_norm _, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  calc
    _ ≤ ∫ z, S.indicator (fun _ => A) z ∂rectangleMeasure F m j k ν :=
      integral_mono_ae hint.norm hI (Filter.Eventually.of_forall hdom)
    _ = _ := by rw [integral_indicator_const _ hS, smul_eq_mul]

/-- The real volume retains the exact scalar Haar normalization. -/
theorem rectangleMeasure_real_box (ν : AdditiveHaarMeasure F)
    (m : Fin 2 → ℕ) (j k e : ℕ) :
    (rectangleMeasure F m j k ν).real
      ((box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) =
      (ν.measure.real ((⟨⟩ : LocalFieldData F).Integers : Set F)) ^
          ((m 0 + 1) * k + j * (m 1 + 1)) *
        (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
          ((m 0 + 1) * k + j * (m 1 + 1))) ^ e := by
  simp only [measureReal_def, rectangleMeasure_box, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_natCast]

/-- The varying part of box volume admits one base before all `j,k`. -/
theorem rectangleMeasure_real_box_le (ν : AdditiveHaarMeasure F)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    (N L : ℕ) :
    (rectangleMeasure F m j k ν).real
      ((box F (m 0 + 1) k (N + L)) ×ˢ (box F j (m 1 + 1) (N + L))) ≤
      ((ν.measure.real ((⟨⟩ : LocalFieldData F).Integers : Set F)) ^
          ((m 0 + 1) * k + j * (m 1 + 1)) *
        (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
          ((m 0 + 1) * k + j * (m 1 + 1))) ^ N) *
      (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
        (2 * (r + 1) * (r + 1))) ^ L := by
  rw [rectangleMeasure_real_box, pow_add _ N L, ← mul_assoc]
  have hq : (1 : ℝ) ≤ (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one.le
  gcongr
  exact rectangle_dimension_le h hr

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- One geometric base bounds the actual integrated raw norm; it precedes the
twist, section, both complementary rectangle dimensions and test vector. -/
def IsKernelNormTorusEnvelope
    (ν : AdditiveHaarMeasure F) (h : ∑ i, (m i + 1) = t + 1)
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (a : Fin t) (B : ℝ) : Prop :=
  ∀ (u : ℝ) (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
    (j k : ℕ) (hr : r = t + (j + k + 1))
    (Wtest : (coefficientModel π lambda).toSubmodule),
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
      ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F),
        c ∈ integralOpen F t →
        let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
        let g := (blockRotation h F)⁻¹ * Iwasawa.torus
          (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c
        let s0 := ((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)
        FiberIntegrable ν ellu f Wtest.val hr s0 g ∧
        ‖representativeKernel ν ellu f Wtest.val hr s0 g‖ ≤
          representativeNormProfile ν ellu f Wtest.val hr s0 g ∧
        0 ≤ representativeNormProfile ν ellu f Wtest.val hr s0 g ∧
        representativeNormProfile ν ellu f Wtest.val hr s0 g ≤
          C * B ^ torusSize lam *
            ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
              (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ)) ∧
        (representativeNormProfile ν ellu f Wtest.val hr s0 g ≠ 0 →
          OppositeCone M (Finset.Iic a.castSucc) lam)

/-- Finite-volume domination and the raw torus majorant give genuine rectangle
fiber convergence and a uniform geometric envelope for its raw-norm integral. -/
theorem exists_kernelNorm_torus_envelope
    (ν : AdditiveHaarMeasure F) (h : ∑ i, (m i + 1) = t + 1)
    (ψ : UnitaryAdditiveCharacter F)
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (lambda : glFunctionals ψ r π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (a : Fin t) (ha : a.val = m 1) :
    ∃ B : ℝ, 1 ≤ B ∧ IsKernelNormTorusEnvelope ν h ψ π lambda τ ell a B := by
  obtain ⟨B, hB, hraw⟩ := exists_rawKernel_torus_majorant F h ψ π hπ lambda τ hτ ell a ha
  let q : ℝ := (⟨⟩ : LocalFieldData F).residueCardinality
  let D : ℝ := q ^ (2 * (r + 1) * (r + 1))
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one.le
  refine ⟨B * D, one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hq),
    fun u f j k hr Wtest => ?_⟩
  obtain ⟨C, N, M, hC0, hC⟩ := hraw u f j k hr Wtest
  let Cv : ℝ := (ν.measure.real ((⟨⟩ : LocalFieldData F).Integers : Set F)) ^
      ((m 0 + 1) * k + j * (m 1 + 1)) *
    (q ^ ((m 0 + 1) * k + j * (m 1 + 1))) ^ N
  have hCv : 0 ≤ Cv := by dsimp only [Cv]; positivity
  refine ⟨Cv * C, M, mul_nonneg hCv hC0, fun lam c hc => ?_⟩
  dsimp only
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)
  let g := (blockRotation h F)⁻¹ * Iwasawa.torus
    (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c
  let s0 : ℂ := ((j + k + 1 : ℕ) : ℂ) / 2 - (j : ℂ)
  have hmeas : AEStronglyMeasurable
      (fun z : Rectangles m j k F => kernel ellu f Wtest.val hr s0 g z.1 z.2)
      (rectangleMeasure F m j k ν) :=
    ((continuous_kernel ellu f π hπ.1.1 lambda Wtest hr s0).comp
      (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable
  have hb : ∀ z : Rectangles m j k F,
      ‖kernel ellu f Wtest.val hr s0 g z.1 z.2‖ ≤
        C * B ^ torusSize lam * q ^
          (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ)) := by
    intro z
    rw [kernel_referenceParameter]
    exact (hC lam c z.1 z.2 hc).1
  have hs : ∀ z : Rectangles m j k F,
      kernel ellu f Wtest.val hr s0 g z.1 z.2 ≠ 0 →
      z ∈ (box F (m 0 + 1) k (N + torusSize lam)) ×ˢ
        (box F j (m 1 + 1) (N + torusSize lam)) := by
    intro z hz
    rw [kernel_referenceParameter] at hz
    exact (hC lam c z.1 z.2 hc).2 hz |>.2
  obtain ⟨hi, hn, hp0, hp⟩ := fiber_integrable_normProfile_le_of_box ν ellu f Wtest.val
    hr s0 g (N + torusSize lam) _ hmeas hb hs
  refine ⟨hi, hn, hp0, hp.trans ?_, ?_⟩
  · calc
      _ ≤ (Cv * D ^ torusSize lam) *
          (C * B ^ torusSize lam * q ^
            (-u * (twistDegree (Finset.Iic a.castSucc) lam : ℝ))) :=
        mul_le_mul_of_nonneg_right
          (rectangleMeasure_real_box_le ν h hr N (torusSize lam)) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  · intro hpne
    by_contra hcone
    have hz : ∀ z : Rectangles m j k F,
        kernel ellu f Wtest.val hr s0 g z.1 z.2 = 0 := by
      intro z
      rw [kernel_referenceParameter]
      by_contra hne
      exact hcone ((hC lam c z.1 z.2 hc).2 hne).1
    apply hpne
    change representativeNormProfile ν ellu f Wtest.val hr s0 g = 0
    simp only [representativeNormProfile, hz, norm_zero, integral_zero]

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
