import Langlands.Global.RankinSelberg.RealGodementCompactSupport
import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Langlands.Representation.RankinSelberg.FiniteCauchyBinet

/-! # Smooth completion of real full-row-rank rectangles -/

noncomputable section

open Langlands.Archimedean
open scoped Matrix.Norms.Operator ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "Y" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (m + 1) ℝ

private def maximalMinor (x : X) (j : Fin (m + 1)) : ℝ :=
  (x.submatrix id j.succAbove).det

/-- Add the signed cofactor row above a rectangular matrix. -/
def completionMatrix (x : X) : Y :=
  Fin.cases (fun j => (-1 : ℝ) ^ j.val * maximalMinor x j) x

@[simp]
theorem lastRows_completionMatrix (x : X) : lastRows (completionMatrix x) = x := by
  ext i j
  simp [lastRows, completionMatrix]

private theorem det_completionMatrix (x : X) :
    (completionMatrix x).det = ∑ j : Fin (m + 1), (maximalMinor x j) ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  have hminor : (completionMatrix x).submatrix Fin.succ j.succAbove =
      x.submatrix id j.succAbove := by
    ext i k
    simp [completionMatrix]
  rw [hminor]
  change (-1 : ℝ) ^ j.val * ((-1 : ℝ) ^ j.val * maximalMinor x j) *
    maximalMinor x j = _
  rw [← mul_assoc, ← mul_pow]
  norm_num
  ring

private theorem exists_maximalMinor_ne_zero {x : X} (hx : HasFullRowRank x) :
    ∃ j : Fin (m + 1), maximalMinor x j ≠ 0 := by
  obtain ⟨b, hb⟩ := hx
  by_contra! h
  have hd := Langlands.GeneralLinear.Spherical.det_rectangular_mul x b
  rw [hb, Matrix.det_one] at hd
  have hminor (S : {s : Finset (Fin (m + 1)) // s.card = m}) :
      (x.submatrix id (S.val.orderEmbOfFin S.property)).det = 0 := by
    obtain ⟨s, hs⟩ := S
    have hcard : (sᶜ : Finset (Fin (m + 1))).card = 1 := by
      rw [Finset.card_compl, Fintype.card_fin, hs]
      omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    have hS : s = ({j} : Finset (Fin (m + 1)))ᶜ := by
      rw [← hj, compl_compl]
    subst s
    change (x.submatrix id ((({j} : Finset (Fin (m + 1)))ᶜ).orderEmbOfFin _)).det = 0
    rw [Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb]
    exact h j
  simp only [hminor, zero_mul, Finset.sum_const_zero] at hd
  exact one_ne_zero hd

theorem det_completionMatrix_pos {x : X} (hx : HasFullRowRank x) :
    0 < (completionMatrix x).det := by
  obtain ⟨j, hj⟩ := exists_maximalMinor_ne_zero hx
  rw [det_completionMatrix]
  exact (sq_pos_of_ne_zero hj).trans_le
    (Finset.single_le_sum (fun i _ => sq_nonneg (maximalMinor x i)) (Finset.mem_univ j))

theorem hasFullRowRank_iff_isUnit_completion (x : X) :
    HasFullRowRank x ↔ IsUnit (completionMatrix x) := by
  refine ⟨fun hx => (Matrix.isUnit_iff_isUnit_det _).mpr (det_completionMatrix_pos hx).ne'.isUnit, ?_⟩
  rintro ⟨g, hg⟩
  refine ⟨(g⁻¹).val.submatrix id Fin.succ, ?_⟩
  ext i j
  have h := congrArg (fun a : Y => a i.succ j.succ) g.mul_inv
  change (g.val * (g⁻¹).val) i.succ j.succ = (1 : Y) i.succ j.succ at h
  rw [hg] at h
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix, completionMatrix] using h

private theorem contDiff_entry_rectangular (i : Fin m) (j : Fin (m + 1)) :
    ContDiff ℝ ∞ (fun x : X => x i j) :=
  (LinearMap.toContinuousLinearMap
    ({ toFun := fun x => x i j
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : X →ₗ[ℝ] ℝ)).contDiff

theorem contDiff_completionMatrix : ContDiff ℝ ∞ (completionMatrix : X → Y) := by
  let fromEntries : (Fin (m + 1) → Fin (m + 1) → ℝ) →ₗ[ℝ] Y :=
    { toFun := Matrix.of
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h : ContDiff ℝ ∞ (fun (x : X) (i j : Fin (m + 1)) => completionMatrix x i j) := by
    apply contDiff_pi.2
    intro i
    apply contDiff_pi.2
    intro j
    refine Fin.cases ?_ (fun i => ?_) i
    · change ContDiff ℝ ∞ (fun x : X => (-1 : ℝ) ^ j.val * maximalMinor x j)
      apply contDiff_const.mul
      let minor : X →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ :=
        { toFun := fun x => x.submatrix id j.succAbove
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hDet : ContDiff ℝ ∞ (Matrix.det : Matrix (Fin m) (Fin m) ℝ → ℝ) :=
        PrincipalSeriesExtension.contDiff_det_comp PrincipalSeriesExtension.contDiff_entry
      exact hDet.comp minor.toContinuousLinearMap.contDiff
    · exact contDiff_entry_rectangular i j
  exact fromEntries.toContinuousLinearMap.contDiff.comp h

theorem isOpen_fullRowRank : IsOpen {x : X | HasFullRowRank x} := by
  have h : {x : X | HasFullRowRank x} =
      completionMatrix ⁻¹' {y : Y | IsUnit y} :=
    Set.ext hasFullRowRank_iff_isUnit_completion
  rw [h]
  exact isOpen_setOf_isUnit_matrix.preimage contDiff_completionMatrix.continuous

/-- Complete a full-row-rank rectangle to an invertible matrix. -/
def completeRows (x : X) (hx : HasFullRowRank x) : G :=
  ((hasFullRowRank_iff_isUnit_completion x).mp hx).unit

theorem completeRows_val (x : X) (hx : HasFullRowRank x) :
    (completeRows x hx).val = completionMatrix x :=
  ((hasFullRowRank_iff_isUnit_completion x).mp hx).unit_spec

theorem lastRows_completeRows (x : X) (hx : HasFullRowRank x) :
    lastRows (completeRows x hx).val = x := by
  rw [completeRows_val, lastRows_completionMatrix]

/-- The full-row-rank chart admits a smooth square completion with positive determinant
and the prescribed trailing rows. -/
def RealGodementRowCompletionStatement : Prop :=
  ∀ m : ℕ,
    ContDiff ℝ ∞ (completionMatrix (m := m)) ∧
    ∀ x : Matrix (Fin m) (Fin (m + 1)) ℝ, HasFullRowRank x →
      0 < (completionMatrix x).det ∧ lastRows (completionMatrix x) = x

theorem realGodementRowCompletion : RealGodementRowCompletionStatement :=
  fun _ => ⟨contDiff_completionMatrix, fun x hx =>
    ⟨det_completionMatrix_pos hx, lastRows_completionMatrix x⟩⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
