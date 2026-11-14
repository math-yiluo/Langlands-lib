import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleBoxes
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstRectangleSupport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceCoordinates
/-! # Lattice boxes for the actual dominant rectangles -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding IsBlockSumRectangularSupport IsLeviFirstRectangularSupport IsLeviSecondRectangularSupport IsTorusRectangleBoxSupport append_mem_integralOpen blockSum_mem_integralOpen box_mono box_mul box_neg_transpose box_of_reverse diagonalRightPermutation_mem_integralOpen dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation exists_blockSum_rectangular_support exists_box_of_isCompact exists_coefficient_blockSum_rootBounded exists_levi_first_rectangular_support exists_levi_second_rectangular_support exists_reindex_blockSum_rectangular_support exists_torus_rectangle_box_support instIsNonarchimedeanLocalFieldCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier_1 integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange isEntryBounded_reflected measurableSet_rectangle_box measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange mem_box_iff_normalizedAbs mem_box_of_mul_mem_box normalizedAbs_ratios_of_rootBounded permutation_mem_integralOpen rectangleBoxesBorel rectangleBoxesMeasurable rectangleBoxesTopology rectangleBoxesValuation rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_box rectangleMeasure_sigmaFinite rectanglesBorel twoBlockDominantBlockSupportLocalInstance1
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
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding determinantNorm_torus determinantNorm_torus_bounds diagonalDensity diagonalDensity_le exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_section_growth exists_standard_functional_growth instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 isEntryBounded_torus normalizedAbs_uniformizer_zpow torusLevi torusLevi_embedding torusLevi_entryBounded torusLevi_inv_halfModulus_le torusLevi_rotated_twist
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open scoped BigOperators NNReal ENNReal

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- Membership in the standard lattice box is an entrywise absolute-value bound. -/
theorem mem_box_iff_normalizedAbs {a b e : ℕ}
    (x : Matrix (Fin a) (Fin b) F) :
    x ∈ box F a b e ↔ ∀ i l, (⟨⟩ : LocalFieldData F).normalizedAbs (x i l) ≤
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ e := by
  set T := (⟨⟩ : LocalFieldData F)
  have hq : (0 : ℝ) < T.residueCardinality := by
    exact_mod_cast (zero_lt_one.trans T.residueCardinality_gt_one)
  have hp : T.normalizedAbs ((T.uniformizer : F) ^ e) =
      ((T.residueCardinality : ℝ) ^ e)⁻¹ := by
    simpa only [zpow_natCast, Units.val_pow_eq_pow_val,
      Langlands.LocalFactor.LocalAbelian.uniformizerUnit_coe, zpow_neg] using
      Langlands.LocalFactor.LocalAbelian.uniformizerUnit_zpow_abs T (e : ℤ)
  change (∀ i l, (T.uniformizer : F) ^ e * x i l ∈ T.Integers) ↔ _
  simp only [← T.normalizedAbs_le_one_iff_mem_integers, T.normalizedAbs_mul, hp]
  constructor
  · intro hx i l
    simpa only [mul_one] using (inv_mul_le_iff₀ (pow_pos hq e)).mp (hx i l)
  · intro hx i l
    exact (inv_mul_le_iff₀ (pow_pos hq e)).mpr (by simpa only [mul_one] using hx i l)

/-- Every compact set of rectangular matrices is contained in one standard box. -/
theorem exists_box_of_isCompact {a b : ℕ}
    {C : Set (Matrix (Fin a) (Fin b) F)} (hC : IsCompact C) :
    ∃ N : ℕ, C ⊆ box F a b N := by
  classical
  set T := (⟨⟩ : LocalFieldData F)
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have hentry : ∀ i : Fin a, ∀ l : Fin b, ∃ N : ℕ,
      ∀ x ∈ C, T.normalizedAbs (x i l) ≤ (T.residueCardinality : ℝ) ^ N := by
    intro i l
    have hcont : Continuous (fun x : Matrix (Fin a) (Fin b) F => x i l) :=
      (continuous_apply l).comp (continuous_apply i)
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn
      (T.continuous_normalizedAbs.comp hcont).continuousOn
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt M hq
    refine ⟨N, fun x hx => ?_⟩
    have hm := hM x hx
    simp only [Function.comp_apply, Real.norm_of_nonneg (T.normalizedAbs_nonneg _)] at hm
    exact hm.trans hN.le
  choose N hN using hentry
  refine ⟨Finset.univ.sup (fun i => Finset.univ.sup (N i)), fun x hx => ?_⟩
  rw [mem_box_iff_normalizedAbs]
  intro i l
  exact (hN i l x hx).trans (pow_le_pow_right₀ hq.le
    ((Finset.le_sup (f := N i) (Finset.mem_univ l)).trans
      (Finset.le_sup (f := fun i => Finset.univ.sup (N i)) (Finset.mem_univ i))))

/-- Multiplication adds entrywise denominator exponents, including for nonsquare matrices. -/
theorem box_mul {a b c N e : ℕ}
    {x : Matrix (Fin a) (Fin b) F} {y : Matrix (Fin b) (Fin c) F}
    (hx : x ∈ box F a b N) (hy : y ∈ box F b c e) :
    x * y ∈ box F a c (N + e) := by
  intro i l
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun d _ => ?_
  rw [show ((⟨⟩ : LocalFieldData F).uniformizer : F) ^ (N + e) *
      (x i d * y d l) =
      (((⟨⟩ : LocalFieldData F).uniformizer : F) ^ N * x i d) *
        (((⟨⟩ : LocalFieldData F).uniformizer : F) ^ e * y d l) by ring]
  exact mul_mem (hx i d) (hy d l)

/-- A bounded inverse removes a right matrix factor at the cost of its exponent. -/
theorem mem_box_of_mul_mem_box {a b N e : ℕ}
    {x : Matrix (Fin a) (Fin b) F} {g : GeneralLinear b F}
    (hx : x * g.val ∈ box F a b N)
    (hg : IsEntryBounded
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) e g) :
    x ∈ box F a b (N + e) := by
  have hgi : g⁻¹.val ∈ box F b b e := fun i l => (hg i l).2
  have hm := box_mul F hx hgi
  simpa only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one] using hm

/-- Negation and transpose preserve the denominator exponent. -/
theorem box_neg_transpose {a b e : ℕ} {x : Matrix (Fin a) (Fin b) F}
    (hx : -x.transpose ∈ box F b a e) : x ∈ box F a b e := by
  intro i l
  have h := neg_mem (hx l i)
  simpa only [Matrix.neg_apply, Matrix.transpose_apply, mul_neg, neg_neg] using h

/-- Row and column reversal preserve the denominator exponent. -/
theorem box_of_reverse {a b e : ℕ} {x : Matrix (Fin a) (Fin b) F}
    (hx : x.submatrix Fin.rev Fin.rev ∈ box F a b e) : x ∈ box F a b e := by
  intro i l
  simpa only [Matrix.submatrix_apply, Fin.rev_rev] using hx i.rev l.rev

/-- Increasing the denominator exponent enlarges the box. -/
theorem box_mono {a b N M : ℕ} (hNM : N ≤ M) :
    box F a b N ⊆ box F a b M := by
  intro x hx
  rw [mem_box_iff_normalizedAbs] at hx ⊢
  have hq : (1 : ℝ) ≤ (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one.le
  exact fun i l => (hx i l).trans (pow_le_pow_right₀ hq hNM)

/-- Reversed inverse transpose preserves the common entry bound. -/
theorem isEntryBounded_reflected {a e : ℕ} {g : GeneralLinear a F}
    (hg : IsEntryBounded
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) e g) :
    IsEntryBounded
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) e
      (weylLong a F * inverseTranspose a F g * weylLong a F) := by
  intro i l
  constructor
  · simpa only [weylLong_conjugate_entry, inverseTranspose_entry] using (hg l.rev i.rev).2
  · simpa only [mul_inv_rev, weylLong_inv, ← mul_assoc, ← map_inv,
      weylLong_conjugate_entry, inverseTranspose_entry, inv_inv] using (hg l.rev i.rev).1

variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- The actual nonzero coefficient restricts both rectangles to a common
box whose exponent is a fixed constant plus the torus size. -/
def IsTorusRectangleBoxSupport
    (ψ : UnitaryAdditiveCharacter F)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ell : glFunctionals ψ r π) (W : (coefficientModel π ell).toSubmodule)
    (N : ℕ) : Prop :=
  ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F),
    c ∈ integralOpen F t →
    W.val.val (matrix h hr (Iwasawa.torus
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c) x y) ≠ 0 →
    x ∈ box F (m 0 + 1) k (N + torusSize lam) ∧
      y ∈ box F j (m 1 + 1) (N + torusSize lam)

/-- Both actual rectangles have a uniform box bound, before all torus and
right integral parameters. -/
theorem exists_torus_rectangle_box_support
    (ψ : UnitaryAdditiveCharacter F)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ N, IsTorusRectangleBoxSupport F ψ h hr π ell W N := by
  obtain ⟨C₀, hC₀, hs₀⟩ := exists_levi_first_rectangular_support F ψ h hr π hπ ell W
  obtain ⟨C₁, hC₁, hs₁⟩ := exists_levi_second_rectangular_support F ψ h hr π hπ ell W
  obtain ⟨N₀, hN₀⟩ := exists_box_of_isCompact F hC₀
  obtain ⟨N₁, hN₁⟩ := exists_box_of_isCompact F hC₁
  refine ⟨max N₀ N₁, fun lam c x y hc hW => ?_⟩
  have hW' :
      W.val.val (matrix h hr
        ((succBlockShape m h).leviEmbedding F (torusLevi F h lam) * c) x y) ≠ 0 := by
    simpa only [torusLevi_embedding] using hW
  have hx := mem_box_of_mul_mem_box F
    (hN₀ (hs₀ (torusLevi F h lam) c x y hc hW'))
    (isEntryBounded_reflected F (torusLevi_entryBounded F h lam 0))
  have hy := mem_box_of_mul_mem_box F
    (hN₁ (hs₁ (torusLevi F h lam) c x y hc hW'))
    (torusLevi_entryBounded F h lam 1)
  exact ⟨box_mono F (Nat.add_le_add_right (le_max_left _ _) _) (box_neg_transpose F hx),
    box_mono F (Nat.add_le_add_right (le_max_right _ _) _) (box_of_reverse F hy)⟩

local instance rectangleBoxesMeasurable : MeasurableSpace F := borel _
local instance rectangleBoxesBorel : BorelSpace F := ⟨rfl⟩

/-- The common box for both actual rectangles is measurable. -/
theorem measurableSet_rectangle_box (m : Fin 2 → ℕ) (j k e : ℕ) :
    MeasurableSet ((box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) :=
  (measurableSet_box F _ _ _).prod (measurableSet_box F _ _ _)

/-- Exact product volume; its exponent counts every entry of both actual rectangles. -/
theorem rectangleMeasure_box
    (ν : AdditiveHaarMeasure F) [MeasureTheory.SigmaFinite ν.measure]
    (m : Fin 2 → ℕ) (j k e : ℕ) :
    rectangleMeasure F m j k ν
        ((box F (m 0 + 1) k e) ×ˢ (box F j (m 1 + 1) e)) =
      ν.measure ((⟨⟩ : LocalFieldData F).Integers : Set F) ^
          ((m 0 + 1) * k + j * (m 1 + 1)) *
        (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ≥0∞) ^
          ((m 0 + 1) * k + j * (m 1 + 1))) ^ e := by
  rw [rectangleMeasure, MeasureTheory.Measure.prod_prod,
    rectangularMeasure_box, rectangularMeasure_box, pow_add, pow_add, mul_pow]
  ring

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
