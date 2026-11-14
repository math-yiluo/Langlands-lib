import Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixGrowth
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceGrowth
noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
open Langlands.RankinSelberg.AdjacentCompactMatrix hiding coefficientDeterminantOrder coefficientDeterminantOrder_spec exists_coefficient_det_growth exists_scaled_integral_of_isCompact instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instValuativeRelCarrier isEntryBounded_of_scaled_integral pow_ord_mul_abs_pow_le uniformizer_pow_ord_div_mem
open Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence

universe uF uV
variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local notation "T" => (⟨⟩ : LocalFieldData F)
local notation "ϖ" => Langlands.LocalFactor.LocalAbelian.uniformizerUnit T

/-- A determinant denominator is cleared by its nonnegative integral order. -/
theorem uniformizer_pow_ord_div_mem (a : Fˣ) :
    (ϖ : F) ^ ((⟨⟩ : LocalFieldData F).ord (a : F)).toNat / (a : F) ∈ (⟨⟩ : LocalFieldData F).Integers := by
  rw [← (⟨⟩ : LocalFieldData F).normalizedAbs_le_one_iff_mem_integers]
  have hq : (1 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  have hq0 : ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ≠ 0 := (zero_lt_one.trans hq).ne'
  change normalizedAbsoluteValue T _ ≤ 1
  rw [map_div₀, map_pow]
  change (⟨⟩ : LocalFieldData F).normalizedAbs (ϖ : F) ^ _ / (⟨⟩ : LocalFieldData F).normalizedAbs (a : F) ≤ 1
  rw [(⟨⟩ : LocalFieldData F).normalizedAbs_of_ne_zero a.ne_zero,
    show (⟨⟩ : LocalFieldData F).normalizedAbs (ϖ : F) = ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ)⁻¹ by
      simpa using Langlands.LocalFactor.LocalAbelian.uniformizerUnit_zpow_abs T 1,
    inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_sub₀ hq0]
  apply zpow_le_one_of_nonpos₀ hq.le
  have := Int.self_le_toNat ((⟨⟩ : LocalFieldData F).ord (a : F))
  omega

/-- Clearing entries and then the determinant clears inverse entries as well. -/
theorem isEntryBounded_of_scaled_integral {r : ℕ}
    (g : GeneralLinear (r + 1) F) (k : ℕ)
    (hg : ∀ i j, (ϖ : F) ^ k * g i j ∈ (⟨⟩ : LocalFieldData F).Integers) :
    IsEntryBounded ϖ ((r + 1) * k + ((⟨⟩ : LocalFieldData F).ord (determinant g : F)).toNat) g := by
  have hϖ : ValuativeRel.valuation F (ϖ : F) ≤ 1 :=
    (uniformizerUnit_isUniformizingElement F).1.le
  have hadj (i j : Fin (r + 1)) :
      (ϖ : F) ^ (r * k) * g.val.adjugate i j ∈ (⟨⟩ : LocalFieldData F).Integers := by
    have h := adjugate_mem_of_forall_mem (⟨⟩ : LocalFieldData F).Integers
      ((ϖ : F) ^ k • g.val) hg i j
    simpa only [Matrix.adjugate_smul, Fintype.card_fin, Nat.add_sub_cancel,
      Matrix.smul_apply, smul_eq_mul, ← pow_mul, Nat.mul_comm k r] using h
  have hginv : g⁻¹.val = (determinant g : F)⁻¹ • g.val.adjugate := by
    simpa only [inv_inv, map_inv, Units.val_inv_eq_inv_val] using
      (val_eq_det_smul_adjugate_inv g⁻¹)
  intro i j
  constructor
  · exact pow_mul_mem_integer_of_le hϖ (by simp only [Nat.add_mul, one_mul]; omega) (hg i j)
  · rw [hginv, Matrix.smul_apply, smul_eq_mul]
    have h := mul_mem (pow_mem (show (ϖ : F) ∈ (⟨⟩ : LocalFieldData F).Integers from hϖ) k)
      (mul_mem (uniformizer_pow_ord_div_mem F (determinant g)) (hadj i j))
    convert h using 1
    simp only [div_eq_mul_inv]
    ring

/-- A single uniformizer power makes every entry in a compact matrix set integral. -/
theorem exists_scaled_integral_of_isCompact {r : ℕ}
    {K : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F)} (hK : IsCompact K) :
    ∃ k : ℕ, ∀ A ∈ K, ∀ i j,
      (ϖ : F) ^ k * A i j ∈ (⟨⟩ : LocalFieldData F).Integers := by
  classical
  have hc : Continuous fun A : Matrix (Fin (r + 1)) (Fin (r + 1)) F =>
      ∑ i, ∑ j, (⟨⟩ : LocalFieldData F).normalizedAbs (A i j) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (⟨⟩ : LocalFieldData F).continuous_normalizedAbs.comp
        ((continuous_apply j).comp (continuous_apply i))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hq : (1 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M hq
  refine ⟨k, fun A hA i j => ?_⟩
  have hentry : (⟨⟩ : LocalFieldData F).normalizedAbs (A i j) ≤ M := by
    calc
      _ ≤ ∑ j, (⟨⟩ : LocalFieldData F).normalizedAbs (A i j) :=
        Finset.single_le_sum (fun j _ => (⟨⟩ : LocalFieldData F).normalizedAbs_nonneg _)
          (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ j, (⟨⟩ : LocalFieldData F).normalizedAbs (A i j) :=
        Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
          (⟨⟩ : LocalFieldData F).normalizedAbs_nonneg _) (Finset.mem_univ i)
      _ ≤ ‖∑ i, ∑ j, (⟨⟩ : LocalFieldData F).normalizedAbs (A i j)‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ M := hM A hA
  rw [← (⟨⟩ : LocalFieldData F).normalizedAbs_le_one_iff_mem_integers]
  change normalizedAbsoluteValue T _ ≤ 1
  rw [map_mul, map_pow,
    show normalizedAbsoluteValue T (ϖ : F) =
        ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ)⁻¹ by
      simpa using Langlands.LocalFactor.LocalAbelian.uniformizerUnit_zpow_abs T 1,
    inv_pow]
  exact (inv_mul_le_one₀ (pow_pos (zero_lt_one.trans hq) k)).2 (hentry.trans hk.le)

/-- The nonnegative determinant order contributes at most a fixed determinant pole. -/
theorem pow_ord_mul_abs_pow_le (B : ℝ) (hB : 0 ≤ B) (N : ℕ)
    (hN : B ≤ ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ N)
    (a : Fˣ) :
    B ^ ((⟨⟩ : LocalFieldData F).ord (a : F)).toNat *
        (⟨⟩ : LocalFieldData F).normalizedAbs (a : F) ^ N ≤
      max 1 ((⟨⟩ : LocalFieldData F).normalizedAbs (a : F) ^ N) := by
  have hq : (0 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    have h : (1 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
      exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
    exact zero_lt_one.trans h
  by_cases hm : 0 ≤ (⟨⟩ : LocalFieldData F).ord (a : F)
  · apply le_trans _ (le_max_left _ _)
    calc
      _ ≤ (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ N) ^
          ((⟨⟩ : LocalFieldData F).ord (a : F)).toNat *
          (⟨⟩ : LocalFieldData F).normalizedAbs (a : F) ^ N := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB hN _)
          (pow_nonneg ((⟨⟩ : LocalFieldData F).normalizedAbs_nonneg _) _)
      _ = 1 := by
        rw [(⟨⟩ : LocalFieldData F).normalizedAbs_of_ne_zero a.ne_zero,
          show (⟨⟩ : LocalFieldData F).ord (a : F) =
              (((⟨⟩ : LocalFieldData F).ord (a : F)).toNat : ℤ) from
            (Int.toNat_of_nonneg hm).symm]
        simp only [Int.toNat_natCast, zpow_neg, zpow_natCast]
        rw [pow_right_comm, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hq.ne'))]
  · simp only [Int.toNat_of_nonpos (le_of_not_ge hm), pow_zero, one_mul]
    exact le_max_right _ _

/-- One determinant-pole order works before all coefficient vectors and all compact
matrix sets, for evaluation at the inverse matrix. -/
theorem exists_coefficient_det_growth (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ) :
    ∃ N : ℕ, ∀ W : (glCoefficientModel ψ r σ ℓ).toSubmodule,
      ∀ K : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F), IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GeneralLinear (r + 1) F, g.val ∈ K →
        ‖glModelFunction ψ r σ ℓ W g⁻¹‖ *
          (⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) ^ N ≤ C := by
  classical
  obtain ⟨B, hB, hgrowth⟩ := Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.exists_coefficient_growth F ψ σ hσ ℓ
  have hq : (1 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt B hq
  refine ⟨N, fun W K hK => ?_⟩
  obtain ⟨k, hk⟩ := exists_scaled_integral_of_isCompact F hK
  obtain ⟨C₀, hC₀, hC⟩ := hgrowth W
  have hc : Continuous fun A : Matrix (Fin (r + 1)) (Fin (r + 1)) F =>
      max (1 : ℝ) ((⟨⟩ : LocalFieldData F).normalizedAbs A.det ^ N) :=
    continuous_const.max (((⟨⟩ : LocalFieldData F).continuous_normalizedAbs.comp
      continuous_id.matrix_det).pow N)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hCB : 0 ≤ C₀ * B ^ ((r + 1) * k) :=
    mul_nonneg hC₀ (pow_nonneg (zero_le_one.trans hB) _)
  refine ⟨C₀ * B ^ ((r + 1) * k) * max M 1,
    mul_nonneg hCB (zero_le_one.trans (le_max_right _ _)), fun g hg => ?_⟩
  have hbounded := isEntryBounded_of_scaled_integral F g k (hk g.val hg)
  have hinv : IsEntryBounded ϖ
      ((r + 1) * k + ((⟨⟩ : LocalFieldData F).ord (determinant g : F)).toNat)
      g⁻¹ := by
    intro i j
    simpa only [inv_inv] using (hbounded i j).symm
  have hmax : max (1 : ℝ)
      ((⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) ^ N) ≤
      max M 1 := by
    apply le_trans _ (le_max_left _ _)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, determinant, Matrix.GeneralLinearGroup.val_det_apply] using hM g.val hg)
  calc
    _ ≤ (C₀ * B ^ ((r + 1) * k +
        ((⟨⟩ : LocalFieldData F).ord (determinant g : F)).toNat)) *
        (⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) ^ N :=
      mul_le_mul_of_nonneg_right (hC _ _ hinv)
        (pow_nonneg ((⟨⟩ : LocalFieldData F).normalizedAbs_nonneg _) _)
    _ = (C₀ * B ^ ((r + 1) * k)) *
        (B ^ ((⟨⟩ : LocalFieldData F).ord (determinant g : F)).toNat *
          (⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) ^ N) := by
      rw [pow_add]
      ring
    _ ≤ (C₀ * B ^ ((r + 1) * k)) *
        max 1 ((⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) ^ N) :=
      mul_le_mul_of_nonneg_left
        (pow_ord_mul_abs_pow_le F B (zero_le_one.trans hB) N hN.le (determinant g)) hCB
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax hCB

/-- A determinant-pole order chosen before the coefficient vector and compact set. -/
def coefficientDeterminantOrder (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ) : ℕ :=
  (exists_coefficient_det_growth F ψ σ hσ ℓ).choose

theorem coefficientDeterminantOrder_spec (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (K : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GeneralLinear (r + 1) F, g.val ∈ K →
      ‖glModelFunction ψ r σ ℓ W g⁻¹‖ *
        (⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) ^
          coefficientDeterminantOrder F ψ σ hσ ℓ ≤ C :=
  (exists_coefficient_det_growth F ψ σ hσ ℓ).choose_spec W K hK

end Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
