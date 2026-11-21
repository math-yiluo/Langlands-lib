import Langlands.Global.RankinSelberg.ComplexWhittakerTranslatedMellin
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerFiniteGrowth

/-! # Polynomial dependence on complex Whittaker right translations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexWhittakerTranslateBound

open Langlands.Archimedean (unitaryCompact)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCharacterChange (complexMatrixHeight_mul_le)
open ComplexLocalIwasawa (alpha bpart kpart npart exp_alpha npart_mul_logTorus_mul_kpart)
open ComplexLocalWhittakerGauge (logTorus logTorus_inv_val)
open ComplexPlaceAnalytic (complexMatrixHeight_inv norm_entry_le_complexMatrixHeight two_le_complexMatrixHeight)
open ComplexWhittakerTranslatedMellin (alpha_right_mul compact_rightTranslate_uniformSimpleRootBound)
open RealConvergenceAnalysis (rootPos)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "H" => complexMatrixHeight

private theorem inverse_diagonal {n : ℕ} (g : G n) (i : Fin n) :
    (Real.exp (-alpha g i) : ℂ) = (bpart g)⁻¹.val i i := by
  have hb : bpart g = (npart g).val * logTorus (alpha g) := by
    unfold bpart
    rw [← mul_inv_cancel_right ((npart g).val * logTorus (alpha g)) (kpart g).val,
      npart_mul_logTorus_mul_kpart]
  have hi : ((npart g).val⁻¹).val i i = 1 :=
    Langlands.GeneralLinear.UpperUnipotent.entry_diag (npart g)⁻¹ i
  rw [hb, mul_inv_rev, Units.val_mul, logTorus_inv_val, Matrix.diagonal_mul, hi, mul_one]

/-- The positive and reciprocal diagonal entries of the triangular part of `k * b` are
bounded by a constant times Jacquet's height of `b`, uniformly over the compact unitary factor. -/
theorem exists_abs_alpha_unitary_mul_le (r : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (k : unitaryCompact ℂ (r + 1)) (b : G (r + 1)) (i : Fin (r + 1)),
      |alpha (k.val * b) i| ≤ Real.log (K * H b) := by
  obtain ⟨L, hL⟩ :=
    (Langlands.Archimedean.ComplexDuality.isCompact_unitaryCompact (r + 1)).exists_bound_of_continuousOn
      (continuous_complexMatrixHeight (r := r)).continuousOn
  let K₀ := max 1 L
  have hK₀ : 1 ≤ K₀ := le_max_left _ _
  have hk (k : unitaryCompact ℂ (r + 1)) : H k.val ≤ K₀ :=
    (le_abs_self _).trans ((by simpa only [Real.norm_eq_abs] using hL k.val k.2 : |H k.val| ≤ L).trans
      (le_max_right _ _))
  refine ⟨K₀ * K₀, one_le_mul_of_one_le_of_one_le hK₀ hK₀, fun k b i => ?_⟩
  have hn : 0 < r + 1 := Nat.succ_pos r
  have hB : H (bpart (k.val * b)) ≤ (K₀ * K₀) * H b := by
    unfold bpart
    have h₁ := (complexMatrixHeight_mul_le k.val b).trans
      (mul_le_mul_of_nonneg_right (hk k) (zero_le_two.trans (two_le_complexMatrixHeight hn b)))
    have h₂ := hk (kpart (k.val * b))⁻¹
    calc
      _ ≤ H (k.val * b) * H ((kpart (k.val * b)).val)⁻¹ := complexMatrixHeight_mul_le _ _
      _ ≤ (K₀ * H b) * K₀ := mul_le_mul h₁ h₂
        (zero_le_two.trans (two_le_complexMatrixHeight hn _))
        (mul_nonneg (zero_le_one.trans hK₀) (zero_le_two.trans (two_le_complexMatrixHeight hn b)))
      _ = _ := by ring
  have hkpos : 0 < K₀ := zero_lt_one.trans_le hK₀
  have hpos : 0 < K₀ * K₀ * H b :=
    mul_pos (mul_pos hkpos hkpos) (zero_lt_two.trans_le (two_le_complexMatrixHeight hn b))
  apply abs_le.mpr
  constructor
  · apply neg_le.mp
    apply Real.exp_le_exp.mp
    have hi := (norm_entry_le_complexMatrixHeight hn (bpart (k.val * b))⁻¹ i i)
    rw [← inverse_diagonal, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
      complexMatrixHeight_inv] at hi
    simpa only [Real.exp_log hpos] using hi.trans hB
  · apply Real.exp_le_exp.mp
    have hi := norm_entry_le_complexMatrixHeight hn (bpart (k.val * b)) i i
    rw [← exp_alpha, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at hi
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
height of the translation. The original growth order and simple-root power on `g` are retained. -/
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
    ((by norm_num : (1 : ℝ) ≤ 2).trans (two_le_complexMatrixHeight (Nat.succ_pos r) b))
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

/-- A fixed complex model vector has one growth order and a polynomial translation loss
for every prescribed simple-root decay order. -/
def ComplexWhittakerTranslateBoundStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ) (W : complexWhittakerModel r ds a),
    ∃ N : ℕ, ∀ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g b : G (r + 1),
      ‖W.val (g * b)‖ ≤ C * H b ^ (N * (r + 1) + 2 * J * r) *
        Real.exp ((N : ℝ) * (∑ i, |alpha g i|) - (J : ℝ) * rootPos (alpha g))

theorem complexWhittakerTranslateBound : ComplexWhittakerTranslateBoundStatement := by
  intro r ds a W
  obtain ⟨K, hK, hLoss⟩ := exists_rightTranslate_loss r
  obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound W {1} isCompact_singleton
  refine ⟨N, fun J => ?_⟩
  obtain ⟨C, hC, hW⟩ := hN J
  let p := N * (r + 1) + 2 * J * r
  refine ⟨C * K ^ p, by positivity, fun g b => ?_⟩
  have hW' (x : G (r + 1)) : ‖W.val x‖ ≤ C *
      Real.exp ((N : ℝ) * (∑ i, |alpha x i|) - (J : ℝ) * rootPos (alpha x)) := by
    simpa only [mul_one] using hW 1 (Set.mem_singleton 1) x
  apply (hLoss W.val N J C hC hW' g b).trans_eq
  change C * (K * H b) ^ p * _ = C * K ^ p * H b ^ p * _
  rw [mul_pow]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexWhittakerTranslateBound
