import Langlands.Global.RankinSelberg.RealGapTriangularChart
import Langlands.Global.RankinSelberg.RealWhittakerGauge
import Langlands.Global.RankinSelberg.RealPrincipalSeriesOrbitWord
import Langlands.Group.GL.LowerBlockQuotientCoordinates
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-! # Logarithmic coordinates and endpoint estimates in the real alternate gap chart -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapAlternateRetained

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (blockSum rankInclusion rankInclusion_mem_upperUnipotent)
open Langlands.RankinSelberg (lastRow_unipotent_mul)
open RealGapTriangularChart (Outer retainedMatrix)
open RealGapUpperTail (firstRectangle packedTail packedTail_mul packedTail_conj packedTail_top_left
  packedTail_top_right packedTail_bottom_left packedTail_bottom_right)
open RealIwasawa (alpha npart kpart npart_mul_torus_mul_kpart alpha_iwasawa torus torus_neg torus_val)
open RealPlaceRestriction (realMatrixHeight_inv)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "N" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "K" => fun n => unitaryCompact ℝ n
local notation "H" => realMatrixHeight
local notation "Head" => fun k => Fin k → ℝ
local notation "Y" => fun q => Fin (q + 1) → ℝ
local notation "Rect" => fun k q => Matrix (Fin k) (Fin (q + 1)) ℝ

private theorem blockSum_mem_unitary {a b : ℕ} {u : G a} {v : G b}
    (hu : u ∈ K a) (hv : v ∈ K b) : blockSum (u, v) ∈ K (a + b) := by
  have hu' := Matrix.mem_unitaryGroup_iff'.mp hu
  have hv' := Matrix.mem_unitaryGroup_iff'.mp hv
  change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks u.val 0 0 v.val) ∈
    Matrix.unitaryGroup (Fin (a + b)) ℝ
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex,
    Matrix.fromBlocks_conjTranspose, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, hu', hv']
  simp

private theorem blockSum_torus {k q : ℕ} (v : Fin k → ℝ) (y : Y q) :
    blockSum (torus v, torus y) = torus (Fin.append v y) := by
  apply Units.ext
  ext i j
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i <;>
    refine Fin.addCases (m := k) (n := q + 1) (fun j₀ => ?_) (fun j₁ => ?_) j
  · simp [torus_val, Matrix.diagonal_apply, Fin.castAdd_inj]
  · have hne : i₀.castAdd (q + 1) ≠ j₁.natAdd k := by
      intro h
      have he := congrArg Fin.val h
      change i₀.val = k + j₁.val at he
      omega
    simp [torus_val, hne]
  · have hne : i₁.natAdd k ≠ j₀.castAdd (q + 1) := by
      intro h
      have he := congrArg Fin.val h
      change k + i₁.val = j₀.val at he
      omega
    simp [torus_val, hne]
  · simp [torus_val, Matrix.diagonal_apply, Fin.natAdd_inj]

private theorem blockSum_one_torus {k q : ℕ} (y : Y q) :
    blockSum ((1 : G k), torus y) = torus (Fin.append (0 : Fin k → ℝ) y) := by
  have h : torus (0 : Fin k → ℝ) = 1 := by
    apply Units.ext
    simp [torus_val, Matrix.diagonal_one]
  rw [← blockSum_torus, h]

private theorem packedTail_zero_one (k q : ℕ) : (packedTail k q 0 1).val = (1 : G (k + q + 1)) := by
  apply Units.ext
  change Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 (1 : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ)) = 1
  rw [Matrix.fromBlocks_one]
  exact map_one (Matrix.reindexRingEquiv ℝ finSumFinEquiv)

private theorem packedTail_rectangle_inv {k q : ℕ} (X : Rect k q) :
    (packedTail k q X 1).val⁻¹ = (packedTail k q (-X) 1).val := by
  apply inv_eq_of_mul_eq_one_right
  rw [← Subgroup.coe_mul, packedTail_mul]
  simp only [Subgroup.coe_one, Units.val_one, Matrix.mul_one, neg_add_cancel, mul_one, packedTail_zero_one]

private theorem alpha_blockSum_torus {k q : ℕ} (g : G k) (y : Y q) :
    alpha (blockSum (g, torus y)) = Fin.append (alpha g) y := by
  let m := q + 1
  let u : N (k + m) := ⟨rankInclusion m (npart g).val, rankInclusion_mem_upperUnipotent (d := m) (npart g).2⟩
  let κ : K (k + m) := ⟨rankInclusion m (kpart g).val,
    blockSum_mem_unitary (kpart g).2 (unitaryCompact ℝ m).one_mem⟩
  have he : blockSum (g, torus y) = u.val * torus (Fin.append (alpha g) y) * κ.val := by
    rw [← blockSum_torus]
    change _ = blockSum ((npart g).val, (1 : G m)) * blockSum (torus (alpha g), torus y) *
      blockSum ((kpart g).val, (1 : G m))
    rw [← map_mul, ← map_mul]
    change _ = blockSum ((npart g).val * torus (alpha g) * (kpart g).val, 1 * torus y * 1)
    rw [one_mul, mul_one, npart_mul_torus_mul_kpart]
  rw [he, alpha_iwasawa]

set_option maxHeartbeats 650000 in
/-- The retained first rectangle and compact factor leave the logarithmic coordinates unchanged. -/
theorem alpha_rankInclusion_mul_retained_inv {k q : ℕ} (g : G k) (p : Outer k q) :
    alpha (rankInclusion (q + 1) g * (retainedMatrix k q p)⁻¹) =
      Fin.append (alpha g) (-p.1.1.2) := by
  let A := rankInclusion (q + 1) g
  let U := packedTail k q (firstRectangle k q p.2) 1
  let u := packedTail k q (g.val * -(firstRectangle k q p.2)) 1
  let D := blockSum ((1 : G k), torus p.1.1.2)
  have hu : A * U.val⁻¹ * A⁻¹ = u.val := by
    dsimp only [U]
    rw [packedTail_rectangle_inv]
    exact packedTail_conj k q g _ 1
  have hD : A * D⁻¹ = blockSum (g, torus (-p.1.1.2)) := by
    change blockSum (g, (1 : G (q + 1))) * (blockSum ((1 : G k), torus p.1.1.2))⁻¹ = _
    rw [← map_inv, ← map_mul]
    change blockSum (g * 1, 1 * (torus p.1.1.2)⁻¹) = _
    rw [mul_one, one_mul, torus_neg]
  have he : A * (retainedMatrix k q p)⁻¹ =
      u.val * blockSum (g, torus (-p.1.1.2)) * p.1.2.val⁻¹ := by
    change A * (p.1.2.val * D * U.val)⁻¹ = _
    rw [← hu, ← hD]
    group
  rw [he, mul_assoc u.val, RealIwasawa.alpha_unipotent_mul]
  let d := blockSum (n := k) (m := q + 1) (g, torus (-p.1.1.2))
  have hα : alpha (d * p.1.2.val⁻¹) = alpha d := by
    conv_lhs => rw [← npart_mul_torus_mul_kpart d]
    rw [mul_assoc]
    exact alpha_iwasawa _ _ (kpart d * p.1.2⁻¹)
  exact hα.trans (alpha_blockSum_torus g _)

private theorem firstRectangle_norm_entry_le {k q : ℕ} (x : Head k) (i : Fin k) (j : Fin (q + 1)) :
    ‖firstRectangle k q x i j‖ ≤ ‖x‖ := by
  refine Fin.cases ?_ (fun j' => ?_) j
  · simpa only [firstRectangle, Fin.cons_zero] using norm_le_pi_norm x i
  · simp only [firstRectangle, Fin.cons_succ, Pi.zero_apply, norm_zero, norm_nonneg]

private theorem packedTail_first_norm_entry_le {k q : ℕ} (x : Head k) (i j : Fin (k + q + 1)) :
    ‖(packedTail k q (firstRectangle k q x) 1).val.val i j‖ ≤ 1 + ‖x‖ := by
  have h (n : ℕ) (i j : Fin n) : ‖(1 : Matrix (Fin n) (Fin n) ℝ) i j‖ ≤ 1 + ‖x‖ := by
    rw [Matrix.one_apply]
    split_ifs
    · simp [norm_nonneg]
    · simp only [norm_zero]; positivity
  refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i <;>
    refine Fin.addCases (m := k) (n := q + 1) (fun j₀ => ?_) (fun j₁ => ?_) j
  · rw [packedTail_top_left]
    exact h k i₀ j₀
  · rw [packedTail_top_right]
    exact (firstRectangle_norm_entry_le x i₀ j₁).trans (le_add_of_nonneg_left zero_le_one)
  · rw [packedTail_bottom_left, norm_zero]
    positivity
  · rw [packedTail_bottom_right]
    exact h (q + 1) i₁ j₁

private theorem firstRectangle_neg {k q : ℕ} (x : Head k) :
    -firstRectangle k q x = firstRectangle k q (-x) := by
  ext i j
  refine Fin.cases ?_ (fun j' => ?_) j <;> simp [firstRectangle]

private theorem height_packedTail_first {k q : ℕ} (x : Head k) :
    H (packedTail k q (firstRectangle k q x) 1).val ≤
      2 * ((k + q + 1 : ℕ) : ℝ) ^ 2 * (1 + ‖x‖) ^ 2 := by
  let U := packedTail k q (firstRectangle k q x) 1
  have hi : U.val⁻¹ = (packedTail k q (firstRectangle k q (-x)) 1).val := by
    dsimp only [U]
    rw [packedTail_rectangle_inv, firstRectangle_neg]
  unfold realMatrixHeight
  change (∑ i : Fin (k + q + 1), ∑ j : Fin (k + q + 1),
    (‖U.val.val i j‖ ^ 2 + ‖U.val⁻¹.val i j‖ ^ 2)) ≤ _
  rw [hi]
  calc
    _ ≤ ∑ _i : Fin (k + q + 1), ∑ _j : Fin (k + q + 1), 2 * (1 + ‖x‖) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      rw [two_mul]
      apply add_le_add (pow_le_pow_left₀ (norm_nonneg _) (packedTail_first_norm_entry_le x i j) 2)
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_neg] using packedTail_first_norm_entry_le (q := q) (-x) i j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The retained height has exponential log-diagonal growth and quadratic growth in the first column. -/
theorem height_retained_le {k q : ℕ} (p : Outer k q) :
    H (retainedMatrix k q p) ≤
      ((1 + 2 * ((k + q + 1 : ℕ) : ℝ) ^ 2) * (2 * ((k + q + 1 : ℕ) : ℝ) ^ 2)) *
        Real.exp (2 * ∑ j, |p.1.1.2 j|) * (1 + ‖p.2‖) ^ 2 := by
  let y : Fin (k + (q + 1)) → ℝ := Fin.append (m := k) (n := q + 1) 0 p.1.1.2
  let U := packedTail k q (firstRectangle k q p.2) 1
  have he : retainedMatrix k q p = p.1.2.val * torus y * U.val := by
    unfold retainedMatrix
    rw [blockSum_one_torus]
  have hS : (∑ i : Fin (k + (q + 1)), |(-y) i|) = ∑ j, |p.1.1.2 j| := by
    refine (Fin.sum_univ_add (a := k) (b := q + 1) (fun i => |(-y) i|)).trans ?_
    simp only [Pi.neg_apply, abs_neg, y, Fin.append_left, Fin.append_right, Pi.zero_apply, abs_zero,
      Finset.sum_const_zero, zero_add]
  have h₁ : H (p.1.2.val * torus y) ≤
      (1 + 2 * ((k + q + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * ∑ j, |p.1.1.2 j|) := by
    have hh := (RealWhittakerGauge.realMatrixHeight_torus_mul_le (r := k + q) (-y) p.1.2⁻¹).trans
      (mul_le_mul_of_nonneg_right (show 2 * (((k + q : ℕ) : ℝ) + 1) ^ 2 ≤
        1 + 2 * ((k + q + 1 : ℕ) : ℝ) ^ 2 by push_cast; linarith) (Real.exp_nonneg _))
    have hh' : H (torus (-y) * (p.1.2⁻¹).val) ≤
        (1 + 2 * ((k + q + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * ∑ j, |p.1.1.2 j|) := by
      rw [← hS]
      exact hh
    rw [torus_neg, Subgroup.coe_inv, ← mul_inv_rev, realMatrixHeight_inv] at hh'
    exact hh'
  rw [he]
  refine (realMatrixHeight_mul_le _ _).trans ?_
  refine (mul_le_mul h₁ (height_packedTail_first (q := q) p.2) ?_ (by positivity)).trans_eq ?_
  · exact zero_le_two.trans (RealPlaceRestriction.two_le_realMatrixHeight (Nat.succ_pos _) _)
  · ring

/-- The first tail column of the retained matrix. -/
def firstRetainedColumn {k q : ℕ} (p : Outer k q) : Fin (k + q + 1) → ℝ :=
  fun i => (retainedMatrix k q p).val i ((0 : Fin (q + 1)).natAdd k)

/-- The last row of the inverse retained matrix. -/
def lastRetainedInverseRow {k q : ℕ} (p : Outer k q) : Fin (k + q + 1) → ℝ :=
  (retainedMatrix k q p)⁻¹.val (Fin.last (k + q))

private theorem norm_mul_unitary_entry_le {n : ℕ} (κ : K n) (v : Fin n → ℝ) (i : Fin n) :
    ‖κ.val.val.mulVec v i‖ ≤ (n : ℝ) * ‖v‖ := by
  rw [Matrix.mulVec, dotProduct]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _j : Fin n, ‖v‖ := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm_mul, ← one_mul ‖v‖]
      exact mul_le_mul (LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup κ.2 i j)
        (norm_le_pi_norm v j) (norm_nonneg _) zero_le_one
    _ = _ := by simp [nsmul_eq_mul]

/-- The first column controls the first rectangle and the positive first logarithm. The last
inverse row controls the negative last logarithm. -/
theorem retained_endpoint_norms {k q : ℕ} (p : Outer k q) :
    ‖p.2‖ ≤ ((k + q + 1 : ℕ) : ℝ) * ‖firstRetainedColumn p‖ ∧
      Real.exp (p.1.1.2 0) ≤ ((k + q + 1 : ℕ) : ℝ) * ‖firstRetainedColumn p‖ ∧
      Real.exp (-p.1.1.2 (Fin.last q)) ≤
        ((k + q + 1 : ℕ) : ℝ) * ‖lastRetainedInverseRow p‖ := by
  let n := k + q + 1
  let κ := p.1.2
  let y := p.1.1.2
  let yall := Fin.append (0 : Fin k → ℝ) y
  let U := packedTail k q (firstRectangle k q p.2) 1
  let B := retainedMatrix k q p
  let j := (0 : Fin (q + 1)).natAdd k
  have hB : B = κ.val * torus yall * U.val := by
    unfold B retainedMatrix
    rw [blockSum_one_torus]
  have hcol (i : Fin n) : κ.val⁻¹.val.mulVec (firstRetainedColumn p) i =
      (torus yall * U.val).val i j := by
    change (κ.val⁻¹ * B).val i j = _
    rw [hB, mul_assoc κ.val, inv_mul_cancel_left]
  have hleading (i : Fin k) : (torus yall * U.val).val (i.castAdd (q + 1)) j = p.2 i := by
    rw [Units.val_mul, torus_val, Matrix.diagonal_mul]
    dsimp only [U, j]
    rw [packedTail_top_right]
    simp [yall, firstRectangle, Fin.append_left, Fin.cons_zero]
  have hfirst : (torus yall * U.val).val j j = Real.exp (y 0) := by
    rw [Units.val_mul, torus_val, Matrix.diagonal_mul]
    dsimp only [U, j]
    rw [packedTail_bottom_right]
    simp [yall, Fin.append_right, Matrix.one_apply_eq]
  refine ⟨(pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_, ?_, ?_⟩
  · have hv := norm_mul_unitary_entry_le κ⁻¹ (firstRetainedColumn p) (i.castAdd (q + 1))
    change ‖κ.val⁻¹.val.mulVec (firstRetainedColumn p) (i.castAdd (q + 1))‖ ≤ _ at hv
    rwa [hcol, hleading] at hv
  · have hv := norm_mul_unitary_entry_le κ⁻¹ (firstRetainedColumn p) j
    change ‖κ.val⁻¹.val.mulVec (firstRetainedColumn p) j‖ ≤ _ at hv
    rw [hcol, hfirst, Real.norm_of_nonneg (Real.exp_nonneg _)] at hv
    exact hv
  · let l := Fin.last (k + q)
    have hl : l = (Fin.last q).natAdd k := Fin.ext rfl
    have hf : Langlands.RankinSelberg.lastRow (B⁻¹ * κ.val) l = Real.exp (-y (Fin.last q)) := by
      have hInv : B⁻¹ * κ.val = U⁻¹.val * (torus yall)⁻¹ := by
        rw [hB, Subgroup.coe_inv]
        group
      rw [hInv, lastRow_unipotent_mul]
      change (torus yall)⁻¹.val l l = _
      rw [← torus_neg, torus_val, Matrix.diagonal_apply_eq, hl]
      simp only [yall, Pi.neg_apply, Fin.append_right]
    have hv : ‖Langlands.RankinSelberg.lastRow (B⁻¹ * κ.val) l‖ ≤ (n : ℝ) * ‖lastRetainedInverseRow p‖ := by
      change ‖∑ i : Fin n, lastRetainedInverseRow p i * κ.val.val i l‖ ≤ _
      refine (norm_sum_le _ _).trans ?_
      calc
        _ ≤ ∑ _i : Fin n, ‖lastRetainedInverseRow p‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, ← mul_one ‖lastRetainedInverseRow p‖]
          exact mul_le_mul (norm_le_pi_norm _ _) (LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup κ.2 i l)
            (norm_nonneg _) (norm_nonneg _)
        _ = _ := by simp [nsmul_eq_mul]
    rw [hf, Real.norm_of_nonneg (Real.exp_nonneg _)] at hv
    exact hv

/-- Coordinate, height and endpoint bounds for the retained term of the triangular Haar chart. -/
def RealGapAlternateRetainedStatement : Prop :=
  ∀ (k q : ℕ) (g : G k) (p : Outer k q),
    alpha (rankInclusion (q + 1) g * (retainedMatrix k q p)⁻¹) = Fin.append (alpha g) (-p.1.1.2) ∧
    H (retainedMatrix k q p) ≤
      ((1 + 2 * ((k + q + 1 : ℕ) : ℝ) ^ 2) * (2 * ((k + q + 1 : ℕ) : ℝ) ^ 2)) *
        Real.exp (2 * ∑ j, |p.1.1.2 j|) * (1 + ‖p.2‖) ^ 2 ∧
    ‖p.2‖ ≤ ((k + q + 1 : ℕ) : ℝ) * ‖firstRetainedColumn p‖ ∧
    Real.exp (p.1.1.2 0) ≤ ((k + q + 1 : ℕ) : ℝ) * ‖firstRetainedColumn p‖ ∧
    Real.exp (-p.1.1.2 (Fin.last q)) ≤ ((k + q + 1 : ℕ) : ℝ) * ‖lastRetainedInverseRow p‖

theorem realGapAlternateRetained : RealGapAlternateRetainedStatement := by
  intro k q g p
  exact ⟨alpha_rankInclusion_mul_retained_inv g p, height_retained_le p, retained_endpoint_norms p⟩

end Langlands.Global.RankinSelbergGlobal.RealGapAlternateRetained
