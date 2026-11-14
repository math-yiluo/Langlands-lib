import Langlands.Representation.RankinSelberg.TwoBlockDominantMatrixGrowth
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRectangleBoxes
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceMajorant
/-! # Geometric coefficient growth on the actual dominant matrices -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding IsBlockSumRectangularSupport IsCoefficientRectangleGrowth IsLeviFirstRectangularSupport IsLeviSecondRectangularSupport IsTorusRectangleBoxSupport append_isEntryBounded append_mem_integralOpen blockSum_mem_integralOpen box_mono box_mul box_neg_transpose box_of_reverse diagonalRightPermutation_mem_integralOpen dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation exists_blockSum_rectangular_support exists_box_of_isCompact exists_coefficient_blockSum_rootBounded exists_levi_first_rectangular_support exists_levi_second_rectangular_support exists_reindex_blockSum_rectangular_support exists_torus_rectangle_box_support instIsNonarchimedeanLocalFieldCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier_1 integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange isEntryBounded_reflected matrixGrowthTopology matrixGrowthValuation matrix_isEntryBounded measurableSet_rectangle_box measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange mem_box_iff_normalizedAbs mem_box_of_mul_mem_box normalizedAbs_ratios_of_rootBounded permutation_mem_integralOpen rectangleBoxesBorel rectangleBoxesMeasurable rectangleBoxesTopology rectangleBoxesValuation rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_box rectangleMeasure_sigmaFinite rectangleUnipotent_isEntryBounded rectanglesBorel twoBlockDominantBlockSupportLocalInstance1
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val unequalRankIwasawaSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement exists_rowSchwartz_order_lower_bound padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding blockRotation_inv_mul_torus determinantNorm_torus determinantNorm_torus_bounds diagonalDensity diagonalDensity_le diagonalDensity_nonneg exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_integrand_torus_majorant exists_rotated_section_growth exists_section_growth exists_standard_functional_growth exists_summable_integrand_majorant instBorelSpaceCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_4 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integrand_standard_mk isEntryBounded_torus normalizedAbs_uniformizer_zpow torusLevi torusLevi_embedding torusLevi_entryBounded torusLevi_inv_halfModulus_le torusLevi_rotated_twist
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open scoped BigOperators NNReal ENNReal

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {t r j k : ℕ} {m : Fin 2 → ℕ}
variable (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))

private theorem rectangleEntries_mul_mem {K : Type*} [Field K] (O : Subring K)
    {a b j k : ℕ} {s : K} {x : Matrix (Fin a) (Fin k) K}
    {y : Matrix (Fin j) (Fin b) K} (hs : s ∈ O)
    (hx : ∀ i l, s * x i l ∈ O) (hy : ∀ i l, s * y i l ∈ O)
    (i l : Coordinates a j k b) : s * rectangleEntries x y i l ∈ O := by
  have hz : s * 0 ∈ O := by rw [mul_zero]; exact O.zero_mem
  have ho : s * 1 ∈ O := by rw [mul_one]; exact hs
  rcases i with i | ((i | (i | i)) | i) <;>
    rcases l with l | ((l | (l | l)) | l) <;>
    simp only [rectangleEntries] <;>
    first | exact hz | exact hx _ _ | exact hy _ _ | split <;> assumption

private theorem rectangleUnipotent_val_mem_box {e : ℕ}
    {x : Matrix (Fin (m 0 + 1)) (Fin k) F}
    {y : Matrix (Fin j) (Fin (m 1 + 1)) F}
    (hx : x ∈ box F (m 0 + 1) k e) (hy : y ∈ box F j (m 1 + 1) e) :
    (rectangleUnipotent h hr x y).val ∈ box F (r + 1) (r + 1) e := by
  have hpow : ((⟨⟩ : LocalFieldData F).uniformizer : F) ^ e ∈
      (⟨⟩ : LocalFieldData F).Integers := by
    rw [← Langlands.LocalFactor.LocalAbelian.uniformizerUnit_coe]
    exact pow_mem (uniformizerUnit_isUniformizingElement F).1.le e
  intro i l
  obtain ⟨i, rfl⟩ := (coordinates h hr).surjective i
  obtain ⟨l, rfl⟩ := (coordinates h hr).surjective l
  rw [rectangleUnipotent_five_entry]
  exact rectangleEntries_mul_mem _ hpow hx hy i l

/-- The actual rectangle matrix and its inverse have the same entry bound. -/
theorem rectangleUnipotent_isEntryBounded {e : ℕ}
    {x : Matrix (Fin (m 0 + 1)) (Fin k) F}
    {y : Matrix (Fin j) (Fin (m 1 + 1)) F}
    (hx : x ∈ box F (m 0 + 1) k e) (hy : y ∈ box F j (m 1 + 1) e) :
    IsEntryBounded (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
      e (rectangleUnipotent h hr x y) := by
  have hx' : -x ∈ box F (m 0 + 1) k e := fun i l => by
    simpa only [Matrix.neg_apply, mul_neg] using neg_mem (hx i l)
  have hy' : -y ∈ box F j (m 1 + 1) e := fun i l => by
    simpa only [Matrix.neg_apply, mul_neg] using neg_mem (hy i l)
  have hv := rectangleUnipotent_val_mem_box F h hr hx hy
  have hi := rectangleUnipotent_val_mem_box F h hr hx' hy'
  intro i l
  constructor
  · exact hv i l
  · rw [rectangleUnipotent_inv]
    exact hi i l

/-- Appending an identity block preserves a common entry bound. -/
theorem append_isEntryBounded {e : ℕ} {g : GeneralLinear (t + 1) F}
    (hg : IsEntryBounded
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) e g) :
    IsEntryBounded (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
      e (append hr g) := by
  have hpow : (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F) :
      F) ^ e ∈ (ValuativeRel.valuation F).integer :=
    pow_mem (uniformizerUnit_isUniformizingElement F).1.le e
  intro i l
  constructor
  · rw [append_entry]
    split_ifs
    · exact (hg _ _).1
    · simpa only [mul_zero] using (zero_mem (ValuativeRel.valuation F).integer)
    · simpa only [mul_one] using hpow
    · simpa only [mul_zero] using (zero_mem (ValuativeRel.valuation F).integer)
  · rw [← map_inv, append_entry]
    split_ifs
    · exact (hg _ _).2
    · simpa only [mul_zero] using (zero_mem (ValuativeRel.valuation F).integer)
    · simpa only [mul_one] using hpow
    · simpa only [mul_zero] using (zero_mem (ValuativeRel.valuation F).integer)

private theorem integralOpen_isEntryBounded_zero {n : ℕ}
    {g : GeneralLinear (n + 1) F} (hg : g ∈ integralOpen F n) :
    IsEntryBounded (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
      0 g := by
  have hg' := (mem_integralOpen F g).mp hg
  intro i l
  simpa only [pow_zero, one_mul] using And.intro (hg'.1 i l) (hg'.2 i l)

/-- Entry bounds for the rectangles and the original group argument add in the
actual JPSS product, including its inverse. -/
theorem matrix_isEntryBounded {e d : ℕ} {g : GeneralLinear (t + 1) F}
    {x : Matrix (Fin (m 0 + 1)) (Fin k) F}
    {y : Matrix (Fin j) (Fin (m 1 + 1)) F}
    (hg : IsEntryBounded
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) d g)
    (hx : x ∈ box F (m 0 + 1) k e) (hy : y ∈ box F j (m 1 + 1) e) :
    IsEntryBounded (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
      (e + d) (matrix h hr g x y) := by
  have hw := integralOpen_isEntryBounded_zero F
    (permutation_mem_integralOpen F r Fin.revPerm)
  have hb : blockWeyl (K := F) h hr ∈ integralOpen F r := by
    rw [blockWeyl_permutation]
    exact permutation_mem_integralOpen F r _
  have hb' := integralOpen_isEntryBounded_zero F hb
  simpa only [zero_add, add_zero, matrix, weylLong] using
    (((hw.mul (rectangleUnipotent_isEntryBounded F h hr hx hy)).mul hb').mul
      (append_isEntryBounded F hr hg))

/-- A common coefficient growth base precedes every coefficient-image vector;
the estimate is uniform in both original rectangles. -/
def IsCoefficientRectangleGrowth
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ell : glFunctionals ψ r π) (B : ℝ) : Prop :=
  ∀ W : (coefficientModel π ell).toSubmodule, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F)
      (x : Matrix (Fin (m 0 + 1)) (Fin k) F)
      (y : Matrix (Fin j) (Fin (m 1 + 1)) F),
      c ∈ integralOpen F t →
      ‖W.val.val (matrix h hr (Iwasawa.torus
        (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c) x y)‖ ≤
        C * B ^ torusSize lam

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
