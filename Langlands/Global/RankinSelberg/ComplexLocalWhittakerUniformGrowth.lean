import Langlands.Global.RankinSelberg.ComplexLocalEqualSimpleRootBound
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerRootDerivative
import Mathlib.Data.Fintype.Powerset

/-! # Simple-root decay from uniform growth of Whittaker derivatives -/

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence

open Langlands.Archimedean Langlands.LocalFactor.Archimedean

variable {r : ℕ}

local notation "I" => Fin (r + 1)
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "Std" => Automorphic.complexStandardKFinite (r + 1)

/-- The growth exponent for a fixed inducing vector is uniform over words in
the simple-root derivatives. The constants for each word are uniform in the
compact factor. -/
def HasUniformSimpleRootDerivativeGrowth {ds : List ComplexCharacterData} (a : ℂˣ)
    (B : Std ds →ₗ[ℂ] (G → ℂ)) (f : Std ds) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ word : List (Fin r),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : I → ℝ) (k : K),
      ‖B (simpleRootStandardWord a k word f) (expDiagonal x * k.val)‖ ≤
        C * Real.exp (M * (positiveLogSum x + positiveLogSum (-x)))

private theorem norm_root_multiplier_product {ι : Type*} (word : List ι) (logRatio : ι → ℝ) :
    ‖(word.map fun i => (Real.exp (logRatio i) : ℂ) * rootCharacterDerivative).prod‖ =
      ‖rootCharacterDerivative‖ ^ word.length * Real.exp (word.map logRatio).sum := by
  induction word with
  | nil => simp
  | cons i word ih =>
    simp only [List.map_cons, List.prod_cons, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _), ih, List.length_cons, List.sum_cons,
      pow_succ, Real.exp_add]
    ring

private theorem sum_repeat_entries {ι : Type*} (word : List ι) (logRatio : ι → ℝ) (j : ℕ) :
    ((word.flatMap (List.replicate j)).map logRatio).sum = (j : ℝ) * (word.map logRatio).sum := by
  induction word with
  | nil => simp
  | cons i word ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, nsmul_eq_mul, ih, List.map_cons, List.sum_cons, mul_add]

private theorem hasSimpleRootLogBound_of_intertwiner {ds : List ComplexCharacterData} {a : ℂˣ}
    {B : Std ds →ₗ[ℂ] (G → ℂ)} (hB : IsComplexWhittakerIntertwiner r ds a B) (f : Std ds)
    (hf : HasUniformSimpleRootDerivativeGrowth a B f) :
    HasSimpleRootLogBound (B f) := by
  classical
  obtain ⟨M, hM, hC⟩ := hf
  choose C hC hbound using hC
  refine ⟨M, hM, fun L _ => ?_⟩
  obtain ⟨j, hj⟩ := exists_nat_ge L
  let repeatRoots (s : Finset (Fin r)) := s.toList.flatMap (List.replicate j)
  let c (s : Finset (Fin r)) := C (repeatRoots s) / ‖rootCharacterDerivative‖ ^ (repeatRoots s).length
  have hc (s : Finset (Fin r)) : 0 ≤ c s := div_nonneg (hC _) (by positivity)
  refine ⟨∑ s, c s, Finset.sum_nonneg fun s _ => hc s, fun x k => ?_⟩
  let d (i : Fin r) := x i.castSucc - x i.succ
  let s : Finset (Fin r) := Finset.univ.filter fun i => 0 ≤ d i
  let word := repeatRoots s
  let g := expDiagonal x * k.val
  let T := positiveLogSum x + positiveLogSum (-x)
  have hsum : (word.map d).sum = (j : ℝ) * simpleRootLogSum x := by
    unfold word repeatRoots
    rw [sum_repeat_entries, Finset.sum_map_toList]
    congr 1
    rw [show s = Finset.univ.filter (fun i => 0 ≤ d i) from rfl, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total 0 (d i) with hi | hi
    · rw [ite_eq_left hi, max_eq_left hi]
    · rw [max_eq_right hi]
      split <;> linarith
  have hword := hbound word x k
  rw [intertwiner_simpleRootWord hB, norm_mul, norm_root_multiplier_product word d, hsum] at hword
  change ‖rootCharacterDerivative‖ ^ word.length *
    Real.exp ((j : ℝ) * simpleRootLogSum x) * ‖B f g‖ ≤ C word * Real.exp (M * T) at hword
  have hγ : 0 < ‖rootCharacterDerivative‖ := norm_pos_iff.mpr rootCharacterDerivative_ne_zero
  have hdiv := (le_div_iff₀ (by positivity :
    0 < ‖rootCharacterDerivative‖ ^ word.length * Real.exp ((j : ℝ) * simpleRootLogSum x))).mpr
      ((mul_comm _ _).trans_le hword)
  have hs : 0 ≤ simpleRootLogSum x := Finset.sum_nonneg fun _ _ => le_max_right _ _
  calc
    ‖B f g‖ ≤ C word * Real.exp (M * T) /
        (‖rootCharacterDerivative‖ ^ word.length * Real.exp ((j : ℝ) * simpleRootLogSum x)) := hdiv
    _ = c s * Real.exp (M * T - (j : ℝ) * simpleRootLogSum x) := by
      rw [Real.exp_sub]
      change _ = (C word / ‖rootCharacterDerivative‖ ^ word.length) * _
      rw [mul_div_mul_comm]
    _ ≤ _ := by
      refine mul_le_mul (Finset.single_le_sum (fun s _ => hc s) (Finset.mem_univ s)) ?_
        (Real.exp_nonneg _) (Finset.sum_nonneg fun s _ => hc s)
      exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hj hs])

private theorem hasSimpleRootLogBound_add {W V : G → ℂ}
    (hW : HasSimpleRootLogBound W) (hV : HasSimpleRootLogBound V) :
    HasSimpleRootLogBound (W + V) := by
  obtain ⟨M, hM, hW⟩ := hW
  obtain ⟨N, hN, hV⟩ := hV
  refine ⟨max M N, hM.trans (le_max_left _ _), fun L hL => ?_⟩
  obtain ⟨C, hC, hW⟩ := hW L hL
  obtain ⟨D, hD, hV⟩ := hV L hL
  refine ⟨C + D, add_nonneg hC hD, fun x k => ?_⟩
  let g := expDiagonal x * k.val
  let T := positiveLogSum x + positiveLogSum (-x)
  let S := simpleRootLogSum x
  have hT : 0 ≤ T :=
    add_nonneg (Finset.sum_nonneg fun _ _ => le_max_right _ _)
      (Finset.sum_nonneg fun _ _ => le_max_right _ _)
  change ‖W g + V g‖ ≤ (C + D) * Real.exp (max M N * T - L * S)
  calc
    _ ≤ C * Real.exp (M * T - L * S) + D * Real.exp (N * T - L * S) :=
      (norm_add_le _ _).trans (add_le_add (hW x k) (hV x k))
    _ ≤ _ := by
      rw [add_mul]
      refine add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD)
      · exact sub_le_sub_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hT) _
      · exact sub_le_sub_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hT) _

private theorem hasSimpleRootLogBound_smul (c : ℂ) {W : G → ℂ} (hW : HasSimpleRootLogBound W) :
    HasSimpleRootLogBound (c • W) := by
  obtain ⟨M, hM, hW⟩ := hW
  refine ⟨M, hM, fun L hL => ?_⟩
  obtain ⟨C, hC, hW⟩ := hW L hL
  refine ⟨‖c‖ * C, by positivity, fun x k => ?_⟩
  simp only [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hW x k) (norm_nonneg _)

/-- Uniform growth on the simple-root derivative words proves the simple-root
bound throughout the Whittaker model, by passage from intertwiner ranges to
their supremum. -/
theorem hasSimpleRootLogBound_of_uniformDerivativeGrowth {ds : List ComplexCharacterData}
    {a : ℂˣ} {W : G → ℂ} (hW : W ∈ complexWhittakerModel r ds a)
    (hGrowth : ∀ (B : Std ds →ₗ[ℂ] (G → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
      ∀ f : Std ds, HasUniformSimpleRootDerivativeGrowth a B f) :
    HasSimpleRootLogBound W := by
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {f | HasSimpleRootLogBound f}
      zero_mem' := ⟨0, le_rfl, fun _ _ => ⟨0, le_rfl, fun _ _ => by simp⟩⟩
      add_mem' := fun h₁ h₂ => hasSimpleRootLogBound_add h₁ h₂
      smul_mem' := fun c _ h => hasSimpleRootLogBound_smul c h }
  have hS : complexWhittakerModel r ds a ≤ S := by
    refine iSup₂_le fun B hB => ?_
    rintro W ⟨f, rfl⟩
    exact hasSimpleRootLogBound_of_intertwiner hB f (hGrowth B hB f)
  exact hS hW

end Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence
