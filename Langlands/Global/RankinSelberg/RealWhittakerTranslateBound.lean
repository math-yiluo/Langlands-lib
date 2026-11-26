import Langlands.Global.RankinSelberg.RealWhittakerTranslatedMellin
import Langlands.Global.RankinSelberg.RealMatrixHeightBounds
import Langlands.Global.RankinSelberg.RealPrincipalSeriesOrbitWord

/-! # Polynomial dependence on real Whittaker right translations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealWhittakerTranslateBound

open Langlands.Archimedean (unitaryCompact)
open Langlands.LocalFactor.Archimedean (RealBlock)
open RealIwasawa (alpha bpart kpart npart exp_alpha npart_mul_torus_mul_kpart torus)
open RealConvergenceAnalysis (rootPos)
open RealWhittakerTranslatedMellin (HasGaugeBound alpha_right_mul compact_rightTranslate_uniformGauge
  hasGaugeBound_of_mem_model)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "H" => realMatrixHeight

private theorem inverse_diagonal {n : ℕ} (g : G n) (i : Fin n) :
    Real.exp (-alpha g i) = (bpart g)⁻¹.val i i := by
  have hb : bpart g = (npart g).val * torus (alpha g) := by
    unfold bpart
    rw [← mul_inv_cancel_right ((npart g).val * torus (alpha g)) (kpart g).val,
      npart_mul_torus_mul_kpart]
  have hi : ((npart g).val⁻¹).val i i = 1 :=
    Langlands.GeneralLinear.UpperUnipotent.entry_diag (npart g)⁻¹ i
  rw [hb, mul_inv_rev, Units.val_mul]
  change Real.exp (-alpha g i) = (Matrix.diagonal (fun j => Real.exp (-alpha g j)) *
    ((npart g).val⁻¹).val) i i
  rw [Matrix.diagonal_mul, hi, mul_one]

/-- The positive and reciprocal diagonal entries of the triangular part of `k * b` are
bounded by a constant times Jacquet's height of `b`, uniformly over the orthogonal factor. -/
theorem exists_abs_alpha_unitary_mul_le (r : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (k : unitaryCompact ℝ (r + 1)) (b : G (r + 1)) (i : Fin (r + 1)),
      |alpha (k.val * b) i| ≤ Real.log (K * H b) := by
  obtain ⟨L, hL⟩ := (isCompact_range ((continuous_realMatrixHeight (m := r + 1)).comp
    (continuous_subtype_val : Continuous fun k : unitaryCompact ℝ (r + 1) =>
      (k : Langlands.GeneralLinear (r + 1) ℝ)))).bddAbove
  let K₀ := max 1 L
  have hK₀ : 1 ≤ K₀ := le_max_left _ _
  have hk (k : unitaryCompact ℝ (r + 1)) : H k.val ≤ K₀ :=
    (hL ⟨k, rfl⟩).trans (le_max_right _ _)
  have hn : 0 < r + 1 := Nat.succ_pos r
  have h2 (g : G (r + 1)) : 2 ≤ H g := RealPlaceRestriction.two_le_realMatrixHeight hn g
  refine ⟨K₀ * K₀, one_le_mul_of_one_le_of_one_le hK₀ hK₀, fun k b i => ?_⟩
  have hB : H (bpart (k.val * b)) ≤ (K₀ * K₀) * H b := by
    unfold bpart
    have h₁ := (realMatrixHeight_mul_le k.val b).trans
      (mul_le_mul_of_nonneg_right (hk k) (zero_le_two.trans (h2 b)))
    have h₂ := hk (kpart (k.val * b))⁻¹
    calc
      _ ≤ H (k.val * b) * H ((kpart (k.val * b)).val)⁻¹ := realMatrixHeight_mul_le _ _
      _ ≤ (K₀ * H b) * K₀ := mul_le_mul h₁ h₂ (zero_le_two.trans (h2 _))
        (mul_nonneg (zero_le_one.trans hK₀) (zero_le_two.trans (h2 b)))
      _ = _ := by ring
  have hkpos : 0 < K₀ := zero_lt_one.trans_le hK₀
  have hpos : 0 < K₀ * K₀ * H b :=
    mul_pos (mul_pos hkpos hkpos) (zero_lt_two.trans_le (h2 b))
  apply abs_le.mpr
  constructor
  · apply neg_le.mp
    apply Real.exp_le_exp.mp
    have hi := RealPlaceRestriction.norm_entry_le_realMatrixHeight hn (bpart (k.val * b))⁻¹ i i
    rw [← inverse_diagonal, Real.norm_of_nonneg (Real.exp_nonneg _),
      RealPlaceRestriction.realMatrixHeight_inv] at hi
    simpa only [Real.exp_log hpos] using hi.trans hB
  · apply Real.exp_le_exp.mp
    have hi := RealPlaceRestriction.norm_entry_le_realMatrixHeight hn (bpart (k.val * b)) i i
    rw [← exp_alpha, Real.norm_of_nonneg (Real.exp_nonneg _)] at hi
    simpa only [Real.exp_log hpos] using hi.trans hB

private theorem rootPos_displacement {r : ℕ} (y z : Fin (r + 1) → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hz : ∀ i, |z i| ≤ L) :
    rootPos y ≤ rootPos (y + z) + (r : ℝ) * (2 * L) := by
  unfold rootPos
  have hSum : (∑ _ : Fin r, 2 * L) = (r : ℝ) * (2 * L) := by simp [nsmul_eq_mul]
  rw [← hSum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply max_le
  · have h₁ := (abs_le.mp (hz i.castSucc)).1
    have h₂ := (abs_le.mp (hz i.succ)).2
    have h₃ := le_max_left ((y + z) i.castSucc - (y + z) i.succ) 0
    simp only [Pi.add_apply] at h₃ ⊢
    linarith
  · exact add_nonneg (le_max_right _ _) (by positivity)

/-- A simple-root bound survives right multiplication with a polynomial loss in the
height of the translation. The original growth order and simple-root power on `g` are
retained. -/
theorem exists_rightTranslate_loss (r : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (W : G (r + 1) → ℂ) (N J : ℕ) (C : ℝ), 0 ≤ C →
      (∀ g, ‖W g‖ ≤ C * Real.exp ((N : ℝ) * (∑ i, |alpha g i|) - (J : ℝ) * rootPos (alpha g))) →
      ∀ g b, ‖W (g * b)‖ ≤ C * (K * H b) ^ (N * (r + 1) + 2 * J * r) *
        Real.exp ((N : ℝ) * (∑ i, |alpha g i|) - (J : ℝ) * rootPos (alpha g)) := by
  obtain ⟨K, hK, hk⟩ := exists_abs_alpha_unitary_mul_le r
  refine ⟨K, hK, fun W N J C hC hW g b => ?_⟩
  let B := K * H b
  let L := Real.log B
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hK
    ((by norm_num : (1 : ℝ) ≤ 2).trans
      (RealPlaceRestriction.two_le_realMatrixHeight (Nat.succ_pos r) b))
  have hL : 0 ≤ L := Real.log_nonneg hB
  let y := alpha g
  let z := alpha ((kpart g).val * b)
  have hz (i : Fin (r + 1)) : |z i| ≤ L := hk (kpart g) b i
  have hLen : (∑ i, |(y + z) i|) ≤ (∑ i, |y i|) + ((r : ℝ) + 1) * L := by
    calc
      _ ≤ ∑ i : Fin (r + 1), (|y i| + L) := Finset.sum_le_sum fun i _ =>
        (abs_add_le _ _).trans (add_le_add_right (hz i) _)
      _ = _ := by simp [Finset.sum_add_distrib, nsmul_eq_mul, Nat.cast_add]
  let p := N * (r + 1) + 2 * J * r
  let E := (N : ℝ) * (∑ i, |y i|) - (J : ℝ) * rootPos y
  have hExp : (N : ℝ) * (∑ i, |(y + z) i|) - (J : ℝ) * rootPos (y + z) ≤ E + (p : ℝ) * L := by
    have h₁ := mul_le_mul_of_nonneg_left hLen (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have h₂ := mul_le_mul_of_nonneg_left (rootPos_displacement y z L hL hz)
      (Nat.cast_nonneg J : (0 : ℝ) ≤ J)
    dsimp only [E, p]
    push_cast
    linarith only [h₁, h₂]
  refine (hW (g * b)).trans ?_
  rw [alpha_right_mul]
  change C * Real.exp ((N : ℝ) * (∑ i, |(y + z) i|) - (J : ℝ) * rootPos (y + z)) ≤
    C * B ^ p * Real.exp E
  calc
    _ ≤ C * Real.exp (E + (p : ℝ) * L) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) hC
    _ = _ := by
      rw [Real.exp_add]
      dsimp only [L]
      rw [← Real.log_pow, Real.exp_log (pow_pos (zero_lt_one.trans_le hB) _)]
      ring

/-- A function with the simple-root gauge bound has one growth order and a polynomial
translation loss for every prescribed simple-root decay order. -/
def RealWhittakerTranslateBoundStatement : Prop :=
  ∀ (r : ℕ) (W : G (r + 1) → ℂ), HasGaugeBound W →
    ∃ N : ℕ, ∀ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g b : G (r + 1),
      ‖W (g * b)‖ ≤ C * H b ^ (N * (r + 1) + 2 * J * r) *
        Real.exp ((N : ℝ) * (∑ i, |alpha g i|) - (J : ℝ) * rootPos (alpha g))

theorem realWhittakerTranslateBound : RealWhittakerTranslateBoundStatement := by
  intro r W hW
  obtain ⟨K, hK, hLoss⟩ := exists_rightTranslate_loss r
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun J => ?_⟩
  obtain ⟨C, hC, hWb⟩ := hN J
  let p := N * (r + 1) + 2 * J * r
  refine ⟨C * K ^ p, by positivity, fun g b => ?_⟩
  have hW' (x : G (r + 1)) : ‖W x‖ ≤ C *
      Real.exp ((N : ℝ) * (∑ i, |alpha x i|) - (J : ℝ) * rootPos (alpha x)) := by
    refine (hWb x).trans_eq ?_
    congr 2
    ring
  apply (hLoss W N J C hC hW' g b).trans_eq
  change C * (K * H b) ^ p * _ = C * K ^ p * H b ^ p * _
  rw [mul_pow]
  ring

/-- Every member of the refined real Whittaker space satisfies the translation bound. -/
theorem translateBound_of_mem_model {r : ℕ} {ds : List RealBlock} {a : ℝˣ}
    {W : G (r + 1) → ℂ} (hW : W ∈ realUniformWhittakerModel r ds a) :
    ∃ N : ℕ, ∀ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g b : G (r + 1),
      ‖W (g * b)‖ ≤ C * H b ^ (N * (r + 1) + 2 * J * r) *
        Real.exp ((N : ℝ) * (∑ i, |alpha g i|) - (J : ℝ) * rootPos (alpha g)) :=
  realWhittakerTranslateBound r W (hasGaugeBound_of_mem_model hW)

end Langlands.Global.RankinSelbergGlobal.RealWhittakerTranslateBound
