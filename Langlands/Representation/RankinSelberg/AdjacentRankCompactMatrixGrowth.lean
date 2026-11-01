import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceGrowth
import Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceProof

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.RankinSelberg.AdjacentCompactMatrix

open HarmonicAnalysis Whittaker GeneralLinear TwoBlockConvergence

universe uF uV
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2

local notation "T" => F.canonicalTopologicalData
local notation "ϖ" => LocalFactor.PadicAbelian.uniformizerUnit T

/-- A determinant denominator is cleared by its nonnegative integral order. -/
theorem uniformizer_pow_ord_div_mem (a : F.Carrierˣ) :
    (ϖ : F.Carrier) ^ (F.canonicalTopologicalData.ord (a : F.Carrier)).toNat / (a : F.Carrier) ∈ F.canonicalTopologicalData.Integers := by
  rw [← F.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers]
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  have hq0 : (F.canonicalTopologicalData.residueCardinality : ℝ) ≠ 0 := (zero_lt_one.trans hq).ne'
  change normalizedAbsoluteValue T _ ≤ 1
  rw [map_div₀, map_pow]
  change F.canonicalTopologicalData.normalizedAbs (ϖ : F.Carrier) ^ _ / F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) ≤ 1
  rw [F.canonicalTopologicalData.normalizedAbs_of_ne_zero a.ne_zero,
    show F.canonicalTopologicalData.normalizedAbs (ϖ : F.Carrier) = (F.canonicalTopologicalData.residueCardinality : ℝ)⁻¹ by
      simpa using LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T 1,
    inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_sub₀ hq0]
  apply zpow_le_one_of_nonpos₀ hq.le
  have := Int.self_le_toNat (F.canonicalTopologicalData.ord (a : F.Carrier))
  omega

/-- Clearing entries and then the determinant clears inverse entries as well. -/
theorem isEntryBounded_of_scaled_integral {r : ℕ}
    (g : GeneralLinear (r + 1) F.Carrier) (k : ℕ)
    (hg : ∀ i j, (ϖ : F.Carrier) ^ k * g i j ∈ F.canonicalTopologicalData.Integers) :
    IsEntryBounded ϖ ((r + 1) * k + (F.canonicalTopologicalData.ord (determinant g : F.Carrier)).toNat) g := by
  have hϖ : ValuativeRel.valuation F.Carrier (ϖ : F.Carrier) ≤ 1 :=
    (uniformizerUnit_isUniformizingElement F).1.le
  have hadj (i j : Fin (r + 1)) :
      (ϖ : F.Carrier) ^ (r * k) * g.val.adjugate i j ∈ F.canonicalTopologicalData.Integers := by
    have h := adjugate_mem_of_forall_mem F.canonicalTopologicalData.Integers
      ((ϖ : F.Carrier) ^ k • g.val) hg i j
    simpa only [Matrix.adjugate_smul, Fintype.card_fin, Nat.add_sub_cancel,
      Matrix.smul_apply, smul_eq_mul, ← pow_mul, Nat.mul_comm k r] using h
  have hginv : g⁻¹.val = (determinant g : F.Carrier)⁻¹ • g.val.adjugate := by
    simpa only [inv_inv, map_inv, Units.val_inv_eq_inv_val] using
      (val_eq_det_smul_adjugate_inv g⁻¹)
  intro i j
  constructor
  · exact pow_mul_mem_integer_of_le hϖ (by simp only [Nat.add_mul, one_mul]; omega) (hg i j)
  · rw [hginv, Matrix.smul_apply, smul_eq_mul]
    have h := mul_mem (pow_mem (show (ϖ : F.Carrier) ∈ F.canonicalTopologicalData.Integers from hϖ) k)
      (mul_mem (uniformizer_pow_ord_div_mem F (determinant g)) (hadj i j))
    convert h using 1
    simp only [div_eq_mul_inv]
    ring


/-- A single uniformizer power makes every entry in a compact matrix set integral. -/
theorem exists_scaled_integral_of_isCompact {r : ℕ}
    {K : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier)} (hK : IsCompact K) :
    ∃ k : ℕ, ∀ A ∈ K, ∀ i j,
      (ϖ : F.Carrier) ^ k * A i j ∈ F.canonicalTopologicalData.Integers := by
  classical
  have hc : Continuous fun A : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier =>
      ∑ i, ∑ j, F.canonicalTopologicalData.normalizedAbs (A i j) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      F.canonicalTopologicalData.continuous_normalizedAbs.comp
        ((continuous_apply j).comp (continuous_apply i))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M hq
  refine ⟨k, fun A hA i j => ?_⟩
  have hentry : F.canonicalTopologicalData.normalizedAbs (A i j) ≤ M := by
    calc
      _ ≤ ∑ j, F.canonicalTopologicalData.normalizedAbs (A i j) :=
        Finset.single_le_sum (fun j _ => F.canonicalTopologicalData.normalizedAbs_nonneg _)
          (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ j, F.canonicalTopologicalData.normalizedAbs (A i j) :=
        Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
          F.canonicalTopologicalData.normalizedAbs_nonneg _) (Finset.mem_univ i)
      _ ≤ ‖∑ i, ∑ j, F.canonicalTopologicalData.normalizedAbs (A i j)‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ M := hM A hA
  rw [← F.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers]
  change normalizedAbsoluteValue T _ ≤ 1
  rw [map_mul, map_pow,
    show normalizedAbsoluteValue T (ϖ : F.Carrier) =
        (F.canonicalTopologicalData.residueCardinality : ℝ)⁻¹ by
      simpa using LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T 1,
    inv_pow]
  exact (inv_mul_le_one₀ (pow_pos (zero_lt_one.trans hq) k)).2 (hentry.trans hk.le)

/-- The nonnegative determinant order contributes at most a fixed determinant pole. -/
theorem pow_ord_mul_abs_pow_le (B : ℝ) (hB : 0 ≤ B) (N : ℕ)
    (hN : B ≤ (F.canonicalTopologicalData.residueCardinality : ℝ) ^ N)
    (a : F.Carrierˣ) :
    B ^ (F.canonicalTopologicalData.ord (a : F.Carrier)).toNat *
        F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) ^ N ≤
      max 1 (F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) ^ N) := by
  have hq : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    have h : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
      exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
    exact zero_lt_one.trans h
  by_cases hm : 0 ≤ F.canonicalTopologicalData.ord (a : F.Carrier)
  · apply le_trans _ (le_max_left _ _)
    calc
      _ ≤ ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ N) ^
          (F.canonicalTopologicalData.ord (a : F.Carrier)).toNat *
          F.canonicalTopologicalData.normalizedAbs (a : F.Carrier) ^ N := by
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB hN _)
          (pow_nonneg (F.canonicalTopologicalData.normalizedAbs_nonneg _) _)
      _ = 1 := by
        rw [F.canonicalTopologicalData.normalizedAbs_of_ne_zero a.ne_zero,
          show F.canonicalTopologicalData.ord (a : F.Carrier) =
              ((F.canonicalTopologicalData.ord (a : F.Carrier)).toNat : ℤ) from
            (Int.toNat_of_nonneg hm).symm]
        simp only [Int.toNat_natCast, zpow_neg, zpow_natCast]
        rw [pow_right_comm, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hq.ne'))]
  · simp only [Int.toNat_of_nonpos (le_of_not_ge hm), pow_zero, one_mul]
    exact le_max_right _ _


/-- One determinant-pole order works before all coefficient vectors and all compact
matrix sets, for evaluation at the inverse matrix. -/
theorem exists_coefficient_det_growth (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ) :
    ∃ N : ℕ, ∀ W : (glCoefficientModel ψ r σ ℓ).toSubmodule,
      ∀ K : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier), IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GeneralLinear (r + 1) F.Carrier, g.val ∈ K →
        ‖glModelFunction ψ r σ ℓ W g⁻¹‖ *
          F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) ^ N ≤ C := by
  classical
  obtain ⟨B, hB, hgrowth⟩ := TwoBlockLowerFixedSlice.exists_coefficient_growth F ψ σ hσ ℓ
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt B hq
  refine ⟨N, fun W K hK => ?_⟩
  obtain ⟨k, hk⟩ := exists_scaled_integral_of_isCompact F hK
  obtain ⟨C₀, hC₀, hC⟩ := hgrowth W
  have hc : Continuous fun A : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier =>
      max (1 : ℝ) (F.canonicalTopologicalData.normalizedAbs A.det ^ N) :=
    continuous_const.max ((F.canonicalTopologicalData.continuous_normalizedAbs.comp
      continuous_id.matrix_det).pow N)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hCB : 0 ≤ C₀ * B ^ ((r + 1) * k) :=
    mul_nonneg hC₀ (pow_nonneg (zero_le_one.trans hB) _)
  refine ⟨C₀ * B ^ ((r + 1) * k) * max M 1,
    mul_nonneg hCB (zero_le_one.trans (le_max_right _ _)), fun g hg => ?_⟩
  have hbounded := isEntryBounded_of_scaled_integral F g k (hk g.val hg)
  have hinv : IsEntryBounded ϖ
      ((r + 1) * k + (F.canonicalTopologicalData.ord (determinant g : F.Carrier)).toNat)
      g⁻¹ := by
    intro i j
    simpa only [inv_inv] using (hbounded i j).symm
  have hmax : max (1 : ℝ)
      (F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) ^ N) ≤
      max M 1 := by
    apply le_trans _ (le_max_left _ _)
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, determinant, Matrix.GeneralLinearGroup.val_det_apply] using hM g.val hg)
  calc
    _ ≤ (C₀ * B ^ ((r + 1) * k +
        (F.canonicalTopologicalData.ord (determinant g : F.Carrier)).toNat)) *
        F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) ^ N :=
      mul_le_mul_of_nonneg_right (hC _ _ hinv)
        (pow_nonneg (F.canonicalTopologicalData.normalizedAbs_nonneg _) _)
    _ = (C₀ * B ^ ((r + 1) * k)) *
        (B ^ (F.canonicalTopologicalData.ord (determinant g : F.Carrier)).toNat *
          F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) ^ N) := by
      rw [pow_add]
      ring
    _ ≤ (C₀ * B ^ ((r + 1) * k)) *
        max 1 (F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) ^ N) :=
      mul_le_mul_of_nonneg_left
        (pow_ord_mul_abs_pow_le F B (zero_le_one.trans hB) N hN.le (determinant g)) hCB
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax hCB

/-- A determinant-pole order chosen before the coefficient vector and compact set. -/
def coefficientDeterminantOrder (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ) : ℕ :=
  (exists_coefficient_det_growth F ψ σ hσ ℓ).choose

theorem coefficientDeterminantOrder_spec (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (K : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GeneralLinear (r + 1) F.Carrier, g.val ∈ K →
      ‖glModelFunction ψ r σ ℓ W g⁻¹‖ *
        F.canonicalTopologicalData.normalizedAbs (determinant g : F.Carrier) ^
          coefficientDeterminantOrder F ψ σ hσ ℓ ≤ C :=
  (exists_coefficient_det_growth F ψ σ hσ ℓ).choose_spec W K hK

end Langlands.RankinSelberg.AdjacentCompactMatrix
