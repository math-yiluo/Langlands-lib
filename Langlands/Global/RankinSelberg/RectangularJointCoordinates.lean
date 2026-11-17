import Langlands.Global.RankinSelberg.AdelicCorrectionArchimedean

/-! # Joint leading-root and rectangular coordinates -/

noncomputable section
universe u
open NumberField
open scoped Classical Matrix.Norms.Elementwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open PrimitiveAdelicHeight Langlands.GeneralLinear.RectangularIwasawa

variable (F : Type u) [Field F] [NumberField F]

/-- Concatenate a tuple of leading roots and the entries of a rectangle,
using the standard finite product equivalence to enumerate the latter. -/
def rectangularJointRow {a d : ℕ} (b : Fin a → Ideles F)
    (x : Matrix (Fin d) (Fin a) (Adeles F)) : RowVector F (a + d * a) :=
  fun _ => Fin.append (fun i => (b i : Adeles F))
    (fun q => x (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)

/-- Bounds for the two components bound the archimedean norm of the
concatenated joint row. -/
theorem rectangularJointRow_archimedean_norm_le
    {a d : ℕ} (b : Fin a → Ideles F)
    (x : Matrix (Fin d) (Fin a) (Adeles F)) (H : ℝ) (hH : 0 ≤ H)
    (hb : ‖archimedeanCoordinates F a (diagonalIdeleRow F b)‖ ≤ H)
    (hx : ‖rectangleArchimedeanCoordinates F d a x‖ ≤ H) :
    ‖archimedeanCoordinates F (a + d * a) (rectangularJointRow F b x)‖ ≤ H := by
  apply (pi_norm_le_iff_of_nonneg hH).mpr
  intro i
  induction i using Fin.addCases with
  | left i =>
    simp only [archimedeanCoordinates, rectangularJointRow, Fin.append_left]
    exact (norm_le_pi_norm (archimedeanCoordinates F a (diagonalIdeleRow F b)) i).trans hb
  | right q =>
    simp only [archimedeanCoordinates, rectangularJointRow, Fin.append_right]
    exact (Matrix.norm_entry_le_entrywise_sup_norm
      (rectangleArchimedeanCoordinates F d a x)).trans hx

/-- Original leading roots are controlled by the corrected root row and
the two-sided correction norm. -/
theorem leading_block_roots_archimedean_norm_le
    {t r : ℕ} (h : t < r) (b : Fin (t + 1) → Ideles F)
    (c : Fin (r + 1) → Ideles F) (H : ℝ) (hH : 0 ≤ H)
    (hc : ‖archimedeanCoordinates F (r + 1) (diagonalIdeleRow F c)‖ ≤ H)
    (hci : ‖archimedeanCoordinates F (r + 1)
      (diagonalIdeleRow F (fun q => (c q)⁻¹))‖ ≤ H) :
    ‖archimedeanCoordinates F (t + 1) (diagonalIdeleRow F (gaugeBlockRootIdeles F t b))‖ ≤
      ‖archimedeanCoordinates F r
        (gaugeSimpleRootRow F r (rectangularCorrectedDiagonal F b c))‖ * H ^ 2 := by
  let Y := archimedeanCoordinates F r
    (gaugeSimpleRootRow F r (rectangularCorrectedDiagonal F b c))
  let C := archimedeanCoordinates F (r + 1) (diagonalIdeleRow F c)
  let Ci := archimedeanCoordinates F (r + 1) (diagonalIdeleRow F (fun q => (c q)⁻¹))
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg Y) (sq_nonneg H))).mpr
  intro i
  let k := Fin.castLE (Nat.succ_le_of_lt h) i
  have he :
      archimedeanAdeleProjection F (gaugeBlockRootIdeles F t b i : Adeles F) =
        Y k * (C k.succ * Ci k.castSucc) := by
    rw [gaugeBlockRootIdeles_eq_corrected_mul_inverse F h b c i]
    have hinv : (gaugeSimpleRootIdeles F r c k)⁻¹ = c k.succ * (c k.castSucc)⁻¹ := by
      simp [gaugeSimpleRootIdeles, div_eq_mul_inv]
    rw [hinv]
    simp only [Units.val_mul, map_mul]
    rfl
  change ‖archimedeanAdeleProjection F (gaugeBlockRootIdeles F t b i : Adeles F)‖ ≤ _
  rw [he]
  have hcorr : ‖C k.succ * Ci k.castSucc‖ ≤ H ^ 2 := by
    apply (norm_mul_le _ _).trans
    rw [pow_two]
    exact mul_le_mul ((norm_le_pi_norm C k.succ).trans hc)
      ((norm_le_pi_norm Ci k.castSucc).trans hci) (norm_nonneg _) hH
  exact (norm_mul_le _ _).trans
    (mul_le_mul (norm_le_pi_norm Y k) hcorr (norm_nonneg _) (norm_nonneg Y))

/-- Common finite multiples for leading roots and rectangle entries give
a common finite multiple for the joint row. -/
theorem rectangularJointRow_finite_integral_multiple
    {a d : ℕ} (b : Fin a → Ideles F)
    (x : Matrix (Fin d) (Fin a) (Adeles F)) (q s : FiniteAdeles F)
    (hq : q ∈ integralFiniteAdeles F) (hs : s ∈ integralFiniteAdeles F)
    (hb : ∀ i, (q * s ^ 2) * (b i : Adeles F).2 ∈ integralFiniteAdeles F)
    (hx : ∀ i j, s * rectangleFiniteCoordinates F d a x i j ∈ integralFiniteAdeles F) :
    ∀ k, (q * s ^ 2) * finiteCoordinates F (a + d * a) (rectangularJointRow F b x) k ∈
      integralFiniteAdeles F := by
  intro k
  induction k using Fin.addCases with
  | left i =>
    simp only [finiteCoordinates, rectangularJointRow, Fin.append_left]
    exact hb i
  | right k =>
    simp only [finiteCoordinates, rectangularJointRow, Fin.append_right]
    have hh := (integralFiniteAdeles F).mul_mem
      ((integralFiniteAdeles F).mul_mem hq hs)
      (hx (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    convert hh using 1
    dsimp only [rectangleFiniteCoordinates]
    ring

end Langlands.Global.RankinSelbergGlobal
