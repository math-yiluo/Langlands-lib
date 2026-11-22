import Langlands.Global.RankinSelberg.ComplexGapInverseTransposeTailBound
import Langlands.Global.RankinSelberg.ComplexGapOrdinaryMajorant

/-! # Matrix height in the alternate complex tail chart -/

noncomputable section

open scoped Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateHeight

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant)
open Langlands.GodementJacquet (complexMatrixHeight_mul_det_bound)
open ArchimedeanLocal (complexNormalizedAbs)
open ComplexGapInverseTransposeTailBound (inverseTailColumns alternateTail_norm_bounds)
open ComplexGapOrdinaryMajorant (normalizedDet_eq_exp)
open ComplexGapTailEndpoints (firstTailColumn)
open ComplexLocalIwasawa (alpha alpha_iwasawa logTorus_neg)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexPlaceAnalytic (complexMatrixHeight_inv)
open ComplexTwoBlockHaar (tailBlockIndex rightTail complexGapTailMatrix complexNormalizedAbs_det_rightTail)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "H" => complexMatrixHeight
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))

private theorem norm_mat_mul_le {k d : ℕ} (X : Mat k d) (B : Mat d d) :
    ‖X * B‖ ≤ (d : ℝ) * (‖X‖ * ‖B‖) := by
  refine (Matrix.norm_le_iff (by positivity)).mpr fun i j => ?_
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ l, ‖X i l * B l j‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin d, ‖X‖ * ‖B‖ := Finset.sum_le_sum fun l _ => by
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm X)
        (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [nsmul_eq_mul]

private theorem inverse_norm_bound {n k : ℕ} (hk : 0 < k) (hkn : k < n)
    (h : G (n - k)) (X : Mat k (n - k)) (v : KU n) :
    let g := rightTail hk hkn h X v
    1 + ‖g⁻¹.val‖ ≤
      (1 + Real.sqrt n * ((↑(n - k) : ℝ) + 1)) * ((1 + ‖X‖) * (1 + ‖h⁻¹.val‖)) := by
  let e := tailBlockIndex hkn
  let g := rightTail hk hkn h X v
  let B := Matrix.reindex e e
    (Matrix.fromBlocks (1 : Mat k k) (-(X * h⁻¹.val)) 0 h⁻¹.val)
  let S := (1 + ‖X‖) * (1 + ‖h⁻¹.val‖)
  let c : ℝ := (↑(n - k) : ℝ) + 1
  have hS : 1 ≤ S := one_le_mul_of_one_le_of_one_le
    (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_right (norm_nonneg _))
  have hc : 1 ≤ c := le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hcS : 1 ≤ c * S := one_le_mul_of_one_le_of_one_le hc hS
  have hB (i j : Fin n) : ‖B i j‖ ≤ c * S := by
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    simp only [B, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
      split_ifs <;> simp [hcS, zero_le_one.trans hcS]
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, norm_neg]
      refine ((Matrix.norm_entry_le_entrywise_sup_norm _).trans (norm_mat_mul_le X h⁻¹.val)).trans ?_
      have hs : ‖X‖ * ‖h⁻¹.val‖ ≤ S :=
        mul_le_mul (le_add_of_nonneg_left zero_le_one) (le_add_of_nonneg_left zero_le_one)
          (norm_nonneg _) (by positivity)
      exact mul_le_mul (le_add_of_nonneg_right zero_le_one) hs
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (zero_le_one.trans hc)
    · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, norm_zero]
      exact zero_le_one.trans hcS
    · rw [Matrix.fromBlocks_apply₂₂]
      refine (Matrix.norm_entry_le_entrywise_sup_norm h⁻¹.val).trans ?_
      calc
        ‖h⁻¹.val‖ ≤ 1 + ‖h⁻¹.val‖ := le_add_of_nonneg_left zero_le_one
        _ ≤ S := le_mul_of_one_le_left (by positivity) (le_add_of_nonneg_right (norm_nonneg _))
        _ ≤ c * S := le_mul_of_one_le_left (zero_le_one.trans hS) hc
  have hg : g⁻¹.val = B * v.val⁻¹.val := (complexGapTailMatrix n k hk hkn h X v).2
  have hnorm : ‖g⁻¹.val‖ ≤ Real.sqrt n * (c * S) := by
    rw [hg]
    refine (Matrix.norm_le_iff (by positivity)).mpr fun i j => ?_
    exact LinearAlgebra.TriangularUnitary.norm_mul_unitary_le (v⁻¹ : KU n).2
      (zero_le_one.trans hcS) hB i j
  change 1 + ‖g⁻¹.val‖ ≤ (1 + Real.sqrt n * c) * S
  nlinarith only [hnorm, hS]

private theorem alpha_tail_inverse {n : ℕ} (z : Fin n → ℝ) (u : N n) :
    alpha (logTorus (-z) * u.val)⁻¹ = z := by
  rw [mul_inv_rev, logTorus_neg, inv_inv]
  change alpha (u⁻¹.val * logTorus z) = z
  simpa only [OneMemClass.coe_one, mul_one] using alpha_iwasawa u⁻¹ z (1 : KU n)

private theorem detAbs_inverse {n : ℕ} (g : G n) : δ g⁻¹ = (δ g)⁻¹ := by
  change ‖(determinant g⁻¹ : ℂ)‖ ^ 2 = (‖(determinant g : ℂ)‖ ^ 2)⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv, inv_pow]

/-- With the upper rectangle supported in its first column, the matrix height is bounded by
powers of the two alternate test arguments and an exponential of the logarithmic tail size. -/
def ComplexGapAlternateHeightStatement : Prop :=
  ∀ (r k : ℕ) (hk : 0 < k) (hkn : k < r + 1), ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
    ∀ (z : Fin (r + 1 - k) → ℝ) (u : N (r + 1 - k)) (x : Fin k → ℂ) (v : KU (r + 1)),
      let X : Mat k (r + 1 - k) := fun i j => if j.val = 0 then x i else 0
      let g := rightTail hk hkn (logTorus (-z) * u.val) X v
      H g ≤ C * (1 + ‖firstTailColumn hk hkn g‖) ^ M *
        (1 + ‖inverseTailColumns hkn g‖) ^ M * Real.exp (2 * ∑ j, |z j|)

set_option maxHeartbeats 700000 in
theorem complexGapAlternateHeight : ComplexGapAlternateHeightStatement := by
  intro r k hk hkn
  let n := r + 1
  let d := n - k
  let c : ℝ := 1 + Real.sqrt n * ((d : ℝ) + 1)
  let C₀ := c * (n : ℝ) * (n : ℝ)
  let C₁ : ℝ := 2 * (n : ℝ) ^ 2 * (n.factorial : ℝ) ^ 2
  let M := 2 * (n + 1)
  have hn : 1 ≤ (n : ℝ) := by dsimp only [n]; exact_mod_cast Nat.succ_pos r
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀, c]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  refine ⟨C₁ * C₀ ^ M, M, by positivity, fun z u x v => ?_⟩
  let X : Mat k d := fun i j => if j.val = 0 then x i else 0
  let h := logTorus (-z) * u.val
  let g := rightTail hk hkn h X v
  let Y := 1 + ‖firstTailColumn hk hkn g‖
  let Z := 1 + ‖inverseTailColumns hkn g‖
  obtain ⟨hX, hInv⟩ := alternateTail_norm_bounds hk hkn h X v
  change ‖x‖ ≤ (n : ℝ) * ‖firstTailColumn hk hkn g‖ at hX
  have hRect : ‖X‖ ≤ ‖x‖ := by
    refine (Matrix.norm_le_iff (norm_nonneg _)).mpr fun i j => ?_
    dsimp only [X]
    split_ifs
    · exact norm_le_pi_norm x i
    · simpa only [norm_zero] using norm_nonneg x
  have hY : 1 + ‖X‖ ≤ (n : ℝ) * Y := by
    dsimp only [Y]
    rw [mul_add, mul_one]
    exact add_le_add hn (hRect.trans hX)
  have hZ : 1 + ‖h⁻¹.val‖ ≤ (n : ℝ) * Z := by
    dsimp only [Z]
    rw [mul_add, mul_one]
    exact add_le_add hn hInv
  have hNorm : 1 + ‖g⁻¹.val‖ ≤ C₀ * (Y * Z) := by
    refine (inverse_norm_bound hk hkn h X v).trans ?_
    calc
      c * ((1 + ‖X‖) * (1 + ‖h⁻¹.val‖)) ≤ c * (((n : ℝ) * Y) * ((n : ℝ) * Z)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul hY hZ (by positivity) (by positivity))
          (by dsimp only [c]; positivity)
      _ = C₀ * (Y * Z) := by dsimp only [C₀]; ring
  have hdet : δ g⁻¹ = Real.exp (2 * ∑ j, z j) := by
    calc
      δ g⁻¹ = (δ g)⁻¹ := detAbs_inverse g
      _ = (δ h)⁻¹ := congrArg Inv.inv (complexNormalizedAbs_det_rightTail hk hkn h X v)
      _ = δ h⁻¹ := (detAbs_inverse h).symm
      _ = Real.exp (2 * ∑ j, alpha h⁻¹ j) := normalizedDet_eq_exp h⁻¹
      _ = _ := congrArg (fun w => Real.exp (2 * ∑ j, w j)) (alpha_tail_inverse z u)
  have hDelta : (δ g⁻¹)⁻¹ ≤ Real.exp (2 * ∑ j, |z j|) := by
    rw [hdet, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have hz := (neg_le_abs (∑ j, z j)).trans (Finset.abs_sum_le_sum_abs _ _)
    linarith
  have hHeight := complexMatrixHeight_mul_det_bound g⁻¹
  rw [complexMatrixHeight_inv] at hHeight
  have hHeight' : H g * δ g⁻¹ ≤ C₁ * (1 + ‖g⁻¹.val‖) ^ M := by
    simpa only [C₁, n, M, Nat.cast_add, Nat.cast_one] using hHeight
  have hH : H g * δ g⁻¹ ≤ C₁ * (C₀ * (Y * Z)) ^ M :=
    hHeight'.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hNorm _) hC₁)
  have hPositive : 0 < δ g⁻¹ := by rw [hdet]; exact Real.exp_pos _
  change H g ≤ (C₁ * C₀ ^ M) * Y ^ M * Z ^ M * Real.exp (2 * ∑ j, |z j|)
  calc
    H g = (H g * δ g⁻¹) * (δ g⁻¹)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hPositive.ne', mul_one]
    _ ≤ (C₁ * (C₀ * (Y * Z)) ^ M) * Real.exp (2 * ∑ j, |z j|) :=
      mul_le_mul hH hDelta (inv_nonneg.mpr hPositive.le) (by
        dsimp only [Y, Z]
        positivity)
    _ = _ := by rw [mul_pow C₀, mul_pow Y]; ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapAlternateHeight
