import Langlands.Global.RankinSelberg.ComplexLocalEqualSimpleRootBound
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerHeights
import Langlands.LinearAlgebra.TriangularUnitary

/-! # Iwasawa logarithms in the last-column recursion -/

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow unipotent_det)
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal (complexNormalizedAbs)
open Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence
open Langlands.Global.RankinSelbergGlobal.Unfolding (norm_matrix_mul_apply_le)

variable {r : ℕ}
local notation "m" => r + 1
local notation "I" => Fin m
local notation "H" => GeneralLinear m ℂ
local notation "U" => upperUnipotent m ℂ
local notation "K" => unitaryCompact ℂ m

/-- The logarithmic torus representatives give a left-unipotent factorization
of each element of the smaller general linear group. -/
theorem exists_unipotent_expDiagonal_unitary (k : H) :
    ∃ (u : U) (x : I → ℝ) (v : K), k = u.val * (expDiagonal x * v.val) := by
  obtain ⟨x, v, hv⟩ := torusPoint_surjective (r := r)
    (Quotient.mk _ k : LeftUnipotentQuotient r ℂ)
  have hrel : k * (expDiagonal x * v.val)⁻¹ ∈ U :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hv)
  exact ⟨⟨_, hrel⟩, x, v, (inv_mul_cancel_right _ _).symm⟩

private theorem exp_neg_coord_le (u : U) (x : I → ℝ) (v : K) (i : I) :
    Real.exp (-x i) ≤ (m : ℝ) * ‖((u.val * (expDiagonal x * v.val))⁻¹).val‖ := by
  let k := u.val * (expDiagonal x * v.val)
  have he : v.val * k⁻¹ = expDiagonal (-x) * (u⁻¹).val := by
    rw [expDiagonal_neg, Subgroup.coe_inv]
    dsimp only [k]
    group
  have hi : (v.val.val * (k⁻¹).val) i i = (Real.exp (-x i) : ℂ) := by
    change (v.val * k⁻¹).val i i = _
    rw [he, Units.val_mul, expDiagonal_val, Matrix.diagonal_mul, UpperUnipotent.entry_diag, mul_one]
    rfl
  have hv := Langlands.LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup
    (show v.val.val ∈ Matrix.unitaryGroup I ℂ from v.property)
  have hb := norm_matrix_mul_apply_le v.val.val (k⁻¹).val hv
    (fun i j => Matrix.norm_entry_le_entrywise_sup_norm (k⁻¹).val (i := i) (j := j)) i i
  rw [hi, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), one_mul] at hb
  simpa only [Nat.cast_add, Nat.cast_one, k] using hb

private theorem exp_last_coord_le (u : U) (x : I → ℝ) (v : K) :
    Real.exp (x (Fin.last r)) ≤ (m : ℝ) * ‖lastRow (u.val * (expDiagonal x * v.val))‖ := by
  let k := u.val * (expDiagonal x * v.val)
  let v' : K := v⁻¹
  have he : k * v'.val = u.val * expDiagonal x := by
    change k * v.val⁻¹ = _
    dsimp only [k]
    group
  have hi : (k.val * v'.val.val) (Fin.last r) (Fin.last r) = (Real.exp (x (Fin.last r)) : ℂ) := by
    change (k * v'.val).val (Fin.last r) (Fin.last r) = _
    rw [he, Units.val_mul, expDiagonal_val, Matrix.mul_diagonal, UpperUnipotent.entry_diag, one_mul]
  have hv := Langlands.LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup
    (show v'.val.val ∈ Matrix.unitaryGroup I ℂ from v'.property)
  let A : Matrix I I ℂ := fun _ j => lastRow k j
  have hA (i j : I) : ‖A i j‖ ≤ ‖lastRow k‖ := norm_le_pi_norm _ j
  have hb := norm_matrix_mul_apply_le A v'.val.val hA hv (Fin.last r) (Fin.last r)
  have hrow : (A * v'.val.val) (Fin.last r) (Fin.last r) =
      (k.val * v'.val.val) (Fin.last r) (Fin.last r) := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rfl
  rw [hrow, hi, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), mul_one] at hb
  simpa only [Nat.cast_add, Nat.cast_one, k] using hb

/-- Every logarithmic direction is controlled by the inverse matrix,
the last row, and the positive simple-root ratios. -/
theorem complexJacquet_logSum_le (u : U) (x : I → ℝ) (v : K) :
    let k := u.val * (expDiagonal x * v.val)
    positiveLogSum x + positiveLogSum (-x) ≤
      (m : ℝ) * (Real.log ((m : ℝ) * (1 + ‖(k⁻¹).val‖)) +
        Real.log ((m : ℝ) * (1 + ‖lastRow k‖)) + simpleRootLogSum x) := by
  let k := u.val * (expDiagonal x * v.val)
  let A := (m : ℝ) * (1 + ‖(k⁻¹).val‖)
  let B := (m : ℝ) * (1 + ‖lastRow k‖)
  have hm : 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_pos r
  have hAn : 1 ≤ 1 + ‖(k⁻¹).val‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hBn : 1 ≤ 1 + ‖lastRow k‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le hm hAn
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hm hBn
  have hS : 0 ≤ simpleRootLogSum x := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hx (i : I) : max (-x i) 0 ≤ Real.log A := by
    refine max_le ?_ (Real.log_nonneg hA)
    rw [← Real.log_exp (-x i)]
    apply Real.log_le_log (Real.exp_pos _)
    refine (exp_neg_coord_le u x v i).trans ?_
    dsimp [A, k]
    gcongr
    exact le_add_of_nonneg_left zero_le_one
  have hlast : x (Fin.last r) ≤ Real.log B := by
    rw [← Real.log_exp (x (Fin.last r))]
    apply Real.log_le_log (Real.exp_pos _)
    refine (exp_last_coord_le u x v).trans ?_
    dsimp [B, k]
    gcongr
    exact le_add_of_nonneg_left zero_le_one
  have hy (i : I) : max (x i) 0 ≤ Real.log B + simpleRootLogSum x :=
    max_le ((Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence.coord_le_last_add_simpleRootLogSum r x i).trans (add_le_add_left hlast _))
      (add_nonneg (Real.log_nonneg hB) hS)
  change positiveLogSum x + positiveLogSum (-x) ≤ (m : ℝ) * (Real.log A + Real.log B + _)
  unfold positiveLogSum
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _ : I, (Real.log A + Real.log B + simpleRootLogSum x) :=
      Finset.sum_le_sum fun i _ => by
        have h := add_le_add (hy i) (hx i)
        change max (x i) 0 + max (-x i) 0 ≤ _
        linarith
    _ = _ := by simp [nsmul_eq_mul, mul_add]

/-- The determinant modulus of the inverse group variable in Iwasawa
coordinates. -/
theorem complexNormalizedAbs_det_inv_iwasawa (u : U) (x : I → ℝ) (v : K) :
    complexNormalizedAbs ((u.val * (expDiagonal x * v.val))⁻¹).val.det =
      Real.exp (-2 * ∑ i, x i) := by
  have hv : ‖(v⁻¹ : K).val.val.det‖ ^ 2 = 1 := by
    have h := ComplexMaximalParabolicIntegration.normSqC_det_unitary v⁻¹
    unfold ComplexMaximalParabolicIntegration.normSqC at h
    exact_mod_cast h
  rw [mul_inv_rev, mul_inv_rev, ← expDiagonal_neg, ← Subgroup.coe_inv, ← Subgroup.coe_inv]
  simp only [complexNormalizedAbs, Units.val_mul, Matrix.det_mul, unipotent_det, expDiagonal_val,
    Matrix.det_diagonal, norm_mul, mul_pow, hv, one_mul, mul_one]
  rw [← Complex.ofReal_prod, ← Real.exp_sum, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _), ← Real.exp_nat_mul]
  change Real.exp ((2 : ℝ) * ∑ i, -(x i)) = _
  rw [Finset.sum_neg_distrib, mul_neg, neg_mul]

private theorem abs_sum_le_positiveLogSums (x : I → ℝ) :
    |∑ i, x i| ≤ positiveLogSum x + positiveLogSum (-x) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [positiveLogSum, positiveLogSum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  change |x i| ≤ max (x i) 0 + max (-x i) 0
  rw [abs_le]
  exact ⟨by linarith [le_max_right (x i) 0, le_max_left (-x i) 0],
    by linarith [le_max_left (x i) 0, le_max_right (-x i) 0]⟩

/-- Simple-root decay absorbs any fixed determinant power in the
recursion, leaving only polynomial growth in the Fourier arguments. -/
theorem exists_complexJacquet_weighted_bound {W : H → ℂ}
    (hU : ∀ (u : U) (k : H), ‖W (u.val * k)‖ = ‖W k‖)
    (hW : HasSimpleRootLogBound W) (t : ℝ) :
    ∃ (b : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ k : H,
      ‖W k‖ * Real.exp (t * Real.log (complexNormalizedAbs (k⁻¹).val.det)) ≤
        C * ((1 + ‖(k⁻¹).val‖) ^ b * (1 + ‖lastRow k‖) ^ b) := by
  obtain ⟨M, hM, hW⟩ := hW
  obtain ⟨b, hb⟩ := exists_nat_ge ((M + 2 * |t|) * (m : ℝ))
  obtain ⟨C, hC, hW⟩ := hW b (Nat.cast_nonneg b)
  refine ⟨b, C * (m : ℝ) ^ (b + b), by positivity, fun k => ?_⟩
  obtain ⟨u, x, v, hk⟩ := exists_unipotent_expDiagonal_unitary k
  let P := positiveLogSum x + positiveLogSum (-x)
  let S := simpleRootLogSum x
  let A := (m : ℝ) * (1 + ‖(k⁻¹).val‖)
  let B := (m : ℝ) * (1 + ‖lastRow k‖)
  have hm : 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_pos r
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le hm
    (show 1 ≤ 1 + ‖(k⁻¹).val‖ from le_add_of_nonneg_right (norm_nonneg _))
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hm
    (show 1 ≤ 1 + ‖lastRow k‖ from le_add_of_nonneg_right (norm_nonneg _))
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hgeom : P ≤ (m : ℝ) * (Real.log A + Real.log B + S) := by
    simpa only [P, S, A, B, hk] using complexJacquet_logSum_le u x v
  have hscale : (M + 2 * |t|) * P ≤ (b : ℝ) * (Real.log A + Real.log B + S) := by
    calc
      _ ≤ (M + 2 * |t|) * ((m : ℝ) * (Real.log A + Real.log B + S)) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = ((M + 2 * |t|) * (m : ℝ)) * (Real.log A + Real.log B + S) := by rw [mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right hb
        (add_nonneg (add_nonneg (Real.log_nonneg hA) (Real.log_nonneg hB)) hS)
  let tdet := t * Real.log (complexNormalizedAbs (k⁻¹).val.det)
  have ht : tdet ≤ 2 * |t| * P := by
    simp only [tdet, hk, complexNormalizedAbs_det_inv_iwasawa, Real.log_exp]
    calc
      _ ≤ |t * (-2 * ∑ i, x i)| := le_abs_self _
      _ = 2 * |t| * |∑ i, x i| := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (abs_sum_le_positiveLogSums x) (by positivity)
  have hWk : ‖W k‖ ≤ C * Real.exp (M * P - b * S) := by
    simpa only [P, S, hk, hU] using hW x v
  have hpow : Real.exp ((b : ℝ) * (Real.log A + Real.log B)) = A ^ b * B ^ b := by
    rw [mul_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (zero_lt_one.trans_le hA), Real.exp_log (zero_lt_one.trans_le hB)]
  change ‖W k‖ * Real.exp tdet ≤ _
  calc
    _ ≤ C * Real.exp (M * P - b * S + tdet) := by
      rw [Real.exp_add, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hWk (Real.exp_nonneg _)
    _ ≤ C * Real.exp ((b : ℝ) * (Real.log A + Real.log B)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
      linarith
    _ = _ := by
      rw [hpow, show A = _ from rfl, show B = _ from rfl, mul_pow, mul_pow, pow_add]
      ring

end Langlands.GodementJacquet
