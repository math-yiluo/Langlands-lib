import Langlands.Representation.Archimedean.RealLeviGeometry
import Langlands.Group.GL.UpperUnipotentEntryCoordinates

/-!
# Tail Gram determinants control the real opposite-cell coordinates

For the transpose of an upper-unipotent real matrix, each tail Gram determinant is at least one
plus the square of every entry in the first row of the tail to the left of the diagonal. The
product of the tail Gram determinants therefore controls all entries.
-/

noncomputable section

open Finset
open scoped Classical Matrix Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealOppositeGramBound

open Langlands.Archimedean.GramFormula (gram)
open Langlands.Archimedean.RealLeviChart (lowerLeft splitDiag splitFactor splitDiag_isLowerTriangular
  splitDiag_apply_self det_splitDiag gram_eq_of_lower one_le_gram_of_lower
  det_le_det_add_transpose_mul_self)

variable {n : ℕ}

local notation "N" => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "M" => Matrix (Fin n) (Fin n) ℝ

private theorem transpose_lower (u : N) : u.val.valᵀ.IsLowerTriangular :=
  fun _ _ h => Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero u h

private theorem transpose_diag (u : N) (p : Fin n) : u.val.valᵀ p p = 1 :=
  Langlands.GeneralLinear.UpperUnipotent.entry_diag u p

/-- Each tail Gram determinant is at least one on the opposite cell. -/
theorem one_le_gram_transpose (u : N) (k : ℕ) : 1 ≤ gram k u.val.valᵀ :=
  one_le_gram_of_lower (transpose_lower u) (transpose_diag u) k

private theorem one_add_sq_le_det (A : M) (i j : Fin n) : 1 + A i j ^ 2 ≤ (1 + A * Aᵀ).det := by
  let c : Fin n → ℝ := fun p => A p j
  let E : M := Matrix.diagonal fun q => if q = j then 0 else 1
  let C : M := E * Aᵀ
  let P : M := Matrix.replicateCol Unit c * Matrix.replicateRow Unit c
  have hP : P = Matrix.vecMulVec c (star c) := by
    ext a b
    simp [P, Matrix.vecMulVec_apply, Matrix.replicateCol, Matrix.replicateRow, Matrix.mul_apply]
  have hA : (1 + P).PosDef := by
    rw [hP]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_vecMulVec_self_star c)
  have hsplit : 1 + A * Aᵀ = (1 + P) + Cᵀ * C := by
    rw [add_assoc]
    congr 1
    ext a b
    simp only [P, C, E, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.replicateCol, Matrix.replicateRow, Matrix.of_apply, Matrix.diagonal_apply,
      Finset.univ_unique, Finset.sum_singleton, c]
    have h (r : Fin n) : A a r * A b r =
        (if r = j then A a j * A b j else 0) +
          (∑ x : Fin n, (if r = x then (if x = j then (0 : ℝ) else 1) else 0) * A a x) *
          (∑ x : Fin n, (if r = x then (if x = j then (0 : ℝ) else 1) else 0) * A b x) := by
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      by_cases hr : r = j
      · subst hr; simp
      · simp [hr]
    rw [Finset.sum_congr rfl fun r _ => h r, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have hdet := det_le_det_add_transpose_mul_self hA C
  rw [← hsplit] at hdet
  have hP' : (1 + P).det = 1 + c ⬝ᵥ c := Matrix.det_one_add_replicateCol_mul_replicateRow c c
  have hsq : A i j ^ 2 ≤ c ⬝ᵥ c := by
    rw [dotProduct]
    have := Finset.single_le_sum (f := fun p => c p * c p) (fun p _ => mul_self_nonneg (c p))
      (Finset.mem_univ i)
    simpa [c, sq] using this
  linarith

private theorem splitDiag_row (u : N) (i : Fin n) (q : Fin n) :
    splitDiag i.val u.val.valᵀ i q = if q = i then 1 else 0 := by
  simp only [splitDiag, Matrix.of_apply]
  by_cases hq : q = i
  · subst hq; simp
  · rw [if_neg hq]
    by_cases hiq : i.val ≤ q.val
    · rw [if_pos (iff_of_true le_rfl hiq)]
      exact Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero u
        (lt_of_le_of_ne (Fin.le_iff_val_le_val.mpr hiq) (Ne.symm hq))
    · rw [if_neg (fun h => hiq (h.mp le_rfl))]

private theorem splitFactor_row (u : N) (i q : Fin n) :
    splitFactor i.val u.val.valᵀ i q = u.val.valᵀ i q := by
  set L := u.val.valᵀ
  set W := splitDiag i.val L
  have hW : IsUnit W.det := by
    rw [det_splitDiag (transpose_lower u) (transpose_diag u)]; exact isUnit_one
  have hrow : Matrix.vecMul (Pi.single i 1) W = Pi.single i 1 := by
    funext q
    rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, one_mul]
      change splitDiag i.val u.val.valᵀ i q = _
      rw [splitDiag_row u i q]
      simp [Pi.single_apply]
    · intro b _ hb; simp [hb]
    · simp
  have hinv : Matrix.vecMul (Pi.single i 1) W⁻¹ = Pi.single i 1 := by
    conv_lhs => rw [← hrow]
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hW, Matrix.vecMul_one]
  have hrowinv (r : Fin n) : W⁻¹ i r = if r = i then 1 else 0 := by
    have h := congrFun hinv r
    rw [Matrix.vecMul, dotProduct, Finset.sum_eq_single i] at h
    · simpa [Pi.single_apply, eq_comm] using h
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  change (W⁻¹ * L) i q = L i q
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hrowinv, if_pos rfl, one_mul]
  · intro b _ hb; rw [hrowinv, if_neg hb, zero_mul]
  · simp

/-- A strict upper entry and the unit principal minor bound the corresponding tail Gram
determinant on the transposed matrix. -/
theorem one_add_sq_entry_le_gram (u : N) {i j : Fin n} (hji : j < i) :
    1 + ‖u.val.val j i‖ ^ 2 ≤ gram i.val u.val.valᵀ := by
  rw [gram_eq_of_lower (transpose_lower u) (transpose_diag u)]
  have h := one_add_sq_le_det (lowerLeft i.val (splitFactor i.val u.val.valᵀ)) i j
  have he : lowerLeft i.val (splitFactor i.val u.val.valᵀ) i j = u.val.val j i := by
    simp only [lowerLeft, Matrix.of_apply]
    rw [if_pos ⟨le_rfl, hji⟩, splitFactor_row]
    rfl
  rw [he] at h
  simpa only [Real.norm_eq_abs, sq_abs] using h

/-- The Gram product over all tail rows of the transpose of an upper-unipotent matrix. -/
def oppositeGramProduct (u : N) : ℝ := ∏ i : Fin n, gram i.val u.val.valᵀ

theorem one_le_oppositeGramProduct (u : N) : 1 ≤ oppositeGramProduct u :=
  Finset.one_le_prod₀ fun i _ => one_le_gram_transpose u i.val

/-- The Gram product controls the square of the largest entrywise displacement from one. -/
def RealOppositeGramBoundStatement : Prop :=
  ∀ (n : ℕ) (u : Langlands.GeneralLinear.upperUnipotent n ℝ),
    1 + ‖u.val.val - 1‖ ^ 2 ≤ oppositeGramProduct u

theorem realOppositeGramBound : RealOppositeGramBoundStatement := by
  intro n u
  have hnonneg : 0 ≤ oppositeGramProduct u - 1 := sub_nonneg.mpr (one_le_oppositeGramProduct u)
  have hsqrt : ‖u.val.val - 1‖ ≤ Real.sqrt (oppositeGramProduct u - 1) := by
    apply (Matrix.norm_le_iff (Real.sqrt_nonneg _)).mpr
    intro i j
    rw [Matrix.sub_apply]
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [Matrix.one_apply_ne hij.ne, sub_zero, Real.le_sqrt (norm_nonneg _) hnonneg]
      have hle : gram j.val u.val.valᵀ ≤ oppositeGramProduct u := by
        simpa only [oppositeGramProduct, max_eq_left (one_le_gram_transpose u _)] using
          Finset.le_prod_max_one (Finset.mem_univ j) (fun k : Fin n => gram k.val u.val.valᵀ)
      linarith [(one_add_sq_entry_le_gram u hij).trans hle]
    · rw [Langlands.GeneralLinear.UpperUnipotent.entry_diag, Matrix.one_apply_eq, sub_self,
        norm_zero]
      positivity
    · rw [Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero u hji, Matrix.one_apply_ne hji.ne',
        sub_zero, norm_zero]
      positivity
  linarith [(Real.le_sqrt (norm_nonneg _) hnonneg).mp hsqrt]

end Langlands.Global.RankinSelbergGlobal.RealOppositeGramBound
