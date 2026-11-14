import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.AllField.LocalField.SmoothCharacterNormProof
import Langlands.AllField.LocalField.SmoothCharacterNormStatement
/-!
# Proof of the real norm decomposition of a smooth scalar character

A character of `F^×` with open kernel has absolute value one on the norm-one
units, because these units form a compact group in which the kernel is an open
subgroup of finite index. Every unit is a norm-one unit times an integer power of
the specified uniformizer, so the absolute value of the character is
`‖ω ϖ‖ ^ ord a`, which is `|a| ^ c` for `c = -log_q ‖ω ϖ‖`. The exponent is
unique because `0 < |ϖ| = q⁻¹ < 1`.
-/

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF


open Langlands.LocalFactor.PadicAbelian hiding uniformizerUnit uniformizerUnit_coe uniformizerUnit_ord uniformizerUnit_zpow_abs uniformizerUnit_zpow_value
open Langlands.LocalFactor.LocalAbelian (uniformizerUnit uniformizerUnit_coe uniformizerUnit_ord uniformizerUnit_zpow_abs uniformizerUnit_zpow_value)

section Helpers

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- A character with open kernel has complex norm one at every unit of
residue-normalized absolute value one. -/
theorem norm_eq_one_of_normalizedAbs_eq_one (ω : Fˣ →* ℂˣ)
    (hω : letI := T.topology; IsOpen (ω.ker : Set Fˣ)) {u : Fˣ}
    (hu : T.normalizedAbs (u : F) = 1) : ‖(ω u : ℂ)‖ = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let N : Fˣ →* ℝ :=
    { toFun := fun a => T.normalizedAbs (a : F)
      map_one' := by simp only [Units.val_one, T.normalizedAbs_one]
      map_mul' := fun a b => by simp only [Units.val_mul, T.normalizedAbs_mul] }
  let K : Subgroup Fˣ := N.ker
  have hK : IsCompact (K : Set Fˣ) := T.isCompact_normalizedAbs_eq_one_units
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : Subgroup K := ω.ker.subgroupOf K
  have hU : IsOpen (U : Set K) := Subgroup.subgroupOf_isOpen K ω.ker hω
  have : Finite (K ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  have hmem := U.pow_index_mem ⟨u, hu⟩
  have h1 : ω u ^ U.index = 1 := by
    have h := Subgroup.mem_subgroupOf.mp hmem
    rw [Subgroup.coe_pow, MonoidHom.mem_ker, map_pow] at h
    exact h
  have h2 : ‖(ω u : ℂ)‖ ^ U.index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) U.index_ne_zero_of_finite).mp h2

/-- A character with open kernel has complex norm `‖ω ϖ‖ ^ ord a` at a unit `a`. -/
theorem norm_eq_norm_uniformizer_zpow_ord (ω : Fˣ →* ℂˣ)
    (hω : letI := T.topology; IsOpen (ω.ker : Set Fˣ)) (a : Fˣ) :
    ‖(ω a : ℂ)‖ = ‖(ω (uniformizerUnit T) : ℂ)‖ ^ T.ord (a : F) := by
  set k := T.ord (a : F)
  let u : Fˣ := a * uniformizerUnit T ^ (-k)
  have hu : T.normalizedAbs (u : F) = 1 := by
    have hq : (T.residueCardinality : ℝ) ≠ 0 := by
      exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one).ne'
    rw [Units.val_mul, T.normalizedAbs_mul, T.normalizedAbs_of_ne_zero a.ne_zero,
      uniformizerUnit_zpow_abs, neg_neg, ← zpow_add₀ hq, neg_add_cancel, zpow_zero]
  have ha : a = u * uniformizerUnit T ^ k := by
    simp only [u, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rw [ha, map_mul, map_zpow, Units.val_mul, norm_mul,
    T.norm_eq_one_of_normalizedAbs_eq_one ω hω hu, one_mul, Units.val_zpow_eq_zpow_val,
    norm_zpow]

end Helpers

/-- Proof of `SmoothCharacterNormDecomposition`: the exponent is
`-log_q ‖ω ϖ‖`, and it is unique since `0 < |ϖ| < 1`. -/
theorem smoothCharacterNormDecomposition (F : Type uF) [Field F] (T : LocalFieldData F) :
    SmoothCharacterNormDecomposition F T := by
  intro ω hω
  have hq1 : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have hq0 : (0 : ℝ) < T.residueCardinality := lt_trans zero_lt_one hq1
  set q : ℝ := (T.residueCardinality : ℝ) with hq
  set r : ℝ := ‖(ω (uniformizerUnit T) : ℂ)‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr (Units.ne_zero _)
  have hdecomp : ∀ a : Fˣ,
      ‖(ω a : ℂ)‖ = T.normalizedAbs (a : F) ^ (-Real.logb q r) := by
    intro a
    rw [T.norm_eq_norm_uniformizer_zpow_ord ω hω a, T.normalizedAbs_of_ne_zero a.ne_zero,
      ← Real.rpow_intCast q, ← Real.rpow_mul hq0.le]
    set k := T.ord (a : F)
    have hk : ((-k : ℤ) : ℝ) * -Real.logb q r = Real.logb q r * (k : ℝ) := by
      push_cast
      ring
    rw [hk, Real.rpow_mul hq0.le, Real.rpow_logb hq0 hq1.ne' hr0, Real.rpow_intCast]
  refine ⟨-Real.logb q r, hdecomp, fun c hc => ?_⟩
  have hπ : T.normalizedAbs ((uniformizerUnit T : Fˣ) : F) = q⁻¹ := by
    simpa only [zpow_one, zpow_neg] using uniformizerUnit_zpow_abs T 1
  have hb0 : 0 < q⁻¹ := inv_pos.mpr hq0
  have hb1 : q⁻¹ ≠ 1 := (inv_lt_one_of_one_lt₀ hq1).ne
  have heq : q⁻¹ ^ c = q⁻¹ ^ (-Real.logb q r) := by
    rw [← hπ, ← hc, ← hdecomp]
  have hlog := congrArg Real.log heq
  rw [Real.log_rpow hb0, Real.log_rpow hb0] at hlog
  exact mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one hb0 hb1) hlog

end Langlands.LocalFieldData
