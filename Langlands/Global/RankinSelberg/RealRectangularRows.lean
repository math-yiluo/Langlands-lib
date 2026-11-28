import Langlands.Global.RankinSelberg.RealUnequalLastRowDescent
import Langlands.Global.RankinSelberg.RealUnequalPairConvergence
import Langlands.Group.GL.LowerTriangularBlockCoordinates
import Langlands.Geometry.Manifold.LinearLieGroup.Units

/-! # Appending one row to a real Rankin–Selberg rectangle -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Global.RankinSelbergGlobal.RealRectangularRows

open ArchimedeanLocal Langlands.Archimedean Langlands.GeneralLinear Langlands.LinearLieGroup
open Langlands.LocalFactor.Archimedean
open RealUnequalLastRowDescent (colEntries colUnip colUnip_mem character_colUnip padGL_mul_colUnip sum_castLE)
open RealUnequalDualConvergence (rect_size rectangularPoint_eq)
open RealUnequalPairConvergence (rectangularPoint_zero index_cases)

local notation "G" => fun n : ℕ => Langlands.GeneralLinear (n + 1) ℝ
local notation "M" => fun n : ℕ => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
local notation "X" => fun j t : ℕ => Matrix (Fin j) (Fin (t + 1)) ℝ
local notation "Row" => fun t : ℕ => Fin (t + 1) → ℝ

variable {r t j : ℕ}

/-- Fill the rows beyond the prefix with zero. -/
def extendRows (k : ℕ) (x : X j t) : X k t :=
  fun i => if hi : i.val < j then x ⟨i.val, hi⟩ else 0

/-- The rectangular point with only the first `j` rows filled. -/
def point (h : t < r) (g : G t) (x : X j t) : G r :=
  ArchimedeanLocal.rectangularPoint h g (extendRows (r - (t + 1)) x)

@[simp] theorem point_zero (h : t < r) (g : G t) (x : X 0 t) :
    point h g x = padGL (Nat.succ_le_succ h.le) g := by
  rw [point, show extendRows (r - (t + 1)) x = 0 by ext i k; simp [extendRows], rectangularPoint_zero]

@[simp] theorem point_full (h : t < r) (g : G t) (x : X (r - (t + 1)) t) :
    point h g x = ArchimedeanLocal.rectangularPoint h g x := by
  rw [point, show extendRows (r - (t + 1)) x = x by ext i k; simp [extendRows, i.isLt]]

private theorem rectangularPoint_entry (h : t < r) (g : G t) (x : X (r - (t + 1)) t)
    (i l : Fin (r + 1)) : (ArchimedeanLocal.rectangularPoint h g x).val i l =
      if hl : l.val < t + 1 then
        if hi : i.val < t + 1 then g.val ⟨i.val, hi⟩ ⟨l.val, hl⟩
        else if hr : i.val < r then x ⟨i.val - (t + 1), by omega⟩ ⟨l.val, hl⟩ else 0
      else (1 : M r) i l := by
  let e := finCongr (rect_size h)
  have hr : t + 1 + (r - (t + 1)) = r := Nat.add_sub_of_le (Nat.succ_le_of_lt h)
  have vF (k : Fin (t + 1)) : (e (lowerBlockFirst (r - (t + 1)) 1 k)).val = k.val := rfl
  have vM (k : Fin (r - (t + 1))) : (e (lowerBlockMiddle (t + 1) 1 k)).val = t + 1 + k.val := rfl
  have vL : (e (lowerBlockLast (t + 1) (r - (t + 1)) 0)).val = r := by change t + 1 + (r - (t + 1)) + 0 = r; omega
  obtain ⟨i', rfl⟩ := e.surjective i
  obtain ⟨l', rfl⟩ := e.surjective l
  rw [rectangularPoint_eq]
  change (lowerBlockLocalization 1 g x 1).val i' l' = _
  rcases index_cases i' with ⟨i', rfl⟩ | ⟨i', rfl⟩ | rfl <;>
  rcases index_cases l' with ⟨l', rfl⟩ | ⟨l', rfl⟩ | rfl <;>
  simp only [lowerBlockLocalization_11, lowerBlockLocalization_12, lowerBlockLocalization_13,
    lowerBlockLocalization_21, lowerBlockLocalization_22, lowerBlockLocalization_23,
    lowerBlockLocalization_31, lowerBlockLocalization_32, lowerBlockLocalization_33, vF, vM, vL]
  · rw [dite_eq_left l'.isLt, dite_eq_left i'.isLt]
  · rw [dite_eq_right (by omega : ¬ t + 1 + l'.val < t + 1), Matrix.one_apply_ne]
    intro he
    have he' := congrArg Fin.val he
    rw [vF, vM] at he'
    omega
  · rw [dite_eq_right (by omega : ¬ r < t + 1), Matrix.one_apply_ne]
    intro he
    have he' := congrArg Fin.val he
    rw [vF, vL] at he'
    omega
  · rw [dite_eq_left l'.isLt, dite_eq_right (by omega : ¬ t + 1 + i'.val < t + 1),
      dite_eq_left (by omega : t + 1 + i'.val < r)]
    congr 1
    apply Fin.ext
    change i'.val = t + 1 + i'.val - (t + 1)
    omega
  · rw [dite_eq_right (by omega : ¬ t + 1 + l'.val < t + 1)]
    change (1 : Matrix (Fin (r - (t + 1))) (Fin (r - (t + 1))) ℝ) i' l' = _
    have he : i' = l' ↔ e (lowerBlockMiddle (t + 1) 1 i') = e (lowerBlockMiddle (t + 1) 1 l') := by
      rw [Fin.ext_iff, Fin.ext_iff, vM, vM, Nat.add_left_cancel_iff]
    simp only [Matrix.one_apply, he]
  · rw [dite_eq_right (by omega : ¬ r < t + 1), Matrix.one_apply_ne]
    intro he
    have he' := congrArg Fin.val he
    rw [vM, vL] at he'
    omega
  · rw [dite_eq_left l'.isLt, dite_eq_right (by omega : ¬ r < t + 1), dite_eq_right (lt_irrefl r)]
  · rw [dite_eq_right (by omega : ¬ t + 1 + l'.val < t + 1), Matrix.one_apply_ne]
    intro he
    have he' := congrArg Fin.val he
    rw [vL, vM] at he'
    omega
  · rw [dite_eq_right (by omega : ¬ r < t + 1), Matrix.one_apply_eq]
    simp only [Matrix.one_apply_eq]

/-- Square-zero directions inserting a row below the first block at offset `j`. -/
def rowDirections (r t j : ℕ) : Row t →ₗ[ℝ] M r where
  toFun y i l := if hl : l.val < t + 1 then if i.val = t + 1 + j then y ⟨l.val, hl⟩ else 0 else 0
  map_add' y z := by
    ext i l
    by_cases hl : l.val ≤ t <;> by_cases hi : i.val = t + 1 + j <;> simp [hl, hi]
  map_smul' c y := by
    ext i l
    by_cases hl : l.val ≤ t <;> by_cases hi : i.val = t + 1 + j <;> simp [hl, hi]

theorem rowDirections_mul (y z : Row t) : rowDirections r t j y * rowDirections r t j z = 0 := by
  ext i l
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : b.val ≤ t
  · have hb' : b.val ≠ t + 1 + j := by omega
    simp [rowDirections, hb']
  · simp [rowDirections, hb]

private theorem exp_rowDirections_val (y : Row t) :
    (Langlands.LinearLieGroup.expUnit (M r) (rowDirections r t j y)).val = 1 + rowDirections r t j y := by
  let A := rowDirections r t j y
  change NormedSpace.exp A = 1 + A
  rw [NormedSpace.exp_eq_tsum ℝ]
  change (∑' k : ℕ, (k.factorial : ℝ)⁻¹ • A ^ k) = 1 + A
  rw [tsum_eq_sum (s := Finset.range 2) (fun k hk => ?_)]
  · simp [Finset.sum_range_succ]
  · have h : 2 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    have hsq : A ^ 2 = 0 := by rw [pow_two, rowDirections_mul]
    rw [← Nat.add_sub_of_le h, pow_add, hsq, zero_mul, smul_zero]

private theorem rectangularPoint_right_add (h : t < r) (g : G t)
    (x y : X (r - (t + 1)) t) :
    ArchimedeanLocal.rectangularPoint h g x * ArchimedeanLocal.rectangularPoint h 1 y = ArchimedeanLocal.rectangularPoint h g (x + y) := by
  simp only [rectangularPoint_eq, RealRectangularIwasawa.rect, lowerBlockLocalization, ← map_mul,
    lowerBlockPair_mul_lowerBlockPair]
  simp

private theorem exp_rowDirections_eq (h : t < r) (hj : j < r - (t + 1)) (y : Row t) :
    Langlands.LinearLieGroup.expUnit (M r) (rowDirections r t j y) = ArchimedeanLocal.rectangularPoint h 1 (Pi.single ⟨j, hj⟩ y) := by
  apply Units.ext
  ext i l
  rw [rectangularPoint_entry, exp_rowDirections_val, Matrix.add_apply]
  have hEntry : rowDirections r t j y i l =
      if hl : l.val < t + 1 then if i.val = t + 1 + j then y ⟨l.val, hl⟩ else 0 else 0 := rfl
  rw [hEntry]
  by_cases hl : l.val < t + 1
  · rw [dite_eq_left hl, dite_eq_left hl]
    by_cases hi : i.val < t + 1
    · rw [dite_eq_left hi, ite_eq_right (by omega : i.val ≠ t + 1 + j), add_zero]
      simp only [Units.val_one, Matrix.one_apply, Fin.ext_iff]
    · have hne : i ≠ l := fun e => hi (e.symm ▸ hl)
      rw [dite_eq_right hi, Matrix.one_apply_ne hne, zero_add]
      by_cases hr : i.val < r
      · rw [dite_eq_left hr]
        by_cases he : i.val = t + 1 + j
        · have hh : (⟨i.val - (t + 1), by omega⟩ : Fin (r - (t + 1))) = ⟨j, hj⟩ :=
            Fin.ext (by change i.val - (t + 1) = j; omega)
          rw [ite_eq_left he, hh, Pi.single_eq_same]
        · have hh : (⟨i.val - (t + 1), by omega⟩ : Fin (r - (t + 1))) ≠ ⟨j, hj⟩ := by
            intro hEq
            have hVal : i.val - (t + 1) = j := congrArg Fin.val hEq
            omega
          rw [ite_eq_right he, Pi.single_eq_of_ne hh]
          rfl
      · rw [dite_eq_right hr, ite_eq_right (by omega : i.val ≠ t + 1 + j)]
  · rw [dite_eq_right hl, dite_eq_right hl, add_zero]

/-- Appending the row is right translation along its lower square-zero directions. -/
theorem point_append (h : t < r) (hj : j < r - (t + 1)) (g : G t) (x : X j t) (y : Row t) :
    point h g (Fin.lastCases y x) = point h g x * Langlands.LinearLieGroup.expUnit (M r) (rowDirections r t j y) := by
  rw [exp_rowDirections_eq h hj, point, point, rectangularPoint_right_add]
  congr 1
  funext i
  change extendRows _ (Fin.lastCases y x) i = extendRows _ x i + (Pi.single ⟨j, hj⟩ y : X (r - (t + 1)) t) i
  by_cases hi : i.val < j
  · have hne : i ≠ ⟨j, hj⟩ := fun e => (Nat.ne_of_lt hi) (congrArg Fin.val e)
    have hs : i.val < j + 1 := by omega
    simp only [extendRows, dite_eq_left hi, dite_eq_left hs, Pi.single_eq_of_ne hne, add_zero]
    rw [show (⟨i.val, hs⟩ : Fin (j + 1)) = Fin.castSucc (⟨i.val, hi⟩ : Fin j) from rfl,
      Fin.lastCases_castSucc]
  · by_cases he : i.val = j
    · have he' : i = ⟨j, hj⟩ := Fin.ext he
      subst i
      rw [Pi.single_eq_same]
      simp only [extendRows, dite_eq_right (lt_irrefl j),
        dite_eq_left (Nat.lt_succ_self j), zero_add]
      rw [show (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) = Fin.last j from rfl, Fin.lastCases_last]
    · have hne : i ≠ ⟨j, hj⟩ := fun e => he (congrArg Fin.val e)
      have hs : ¬ i.val < j + 1 := by omega
      simp only [extendRows, dite_eq_right hi, dite_eq_right hs, Pi.single_eq_of_ne hne, add_zero]

/-- The first block and the filled rectangle, without the final identity coordinates. -/
def leadingBlock (g : G t) (x : X j t) : Langlands.GeneralLinear (t + 1 + j) ℝ := lowerBlockPair g x 1

/-- Reading the rectangle with its trailing identity coordinates as an ordinary group padding. -/
theorem point_eq_pad (h : t < r) (hj : j ≤ r - (t + 1)) (g : G t) (x : X j t) :
    point h g x = padGL (by omega : t + 1 + j ≤ r + 1) (leadingBlock g x) := by
  apply Units.ext
  ext i l
  rw [point, rectangularPoint_entry, UnequalAnalytic.padGL_apply]
  by_cases hl : l.val < t + 1
  · have hl' : l.val < t + 1 + j := by omega
    rw [dite_eq_left hl]
    by_cases hi : i.val < t + 1
    · have hi' : i.val < t + 1 + j := by omega
      rw [dite_eq_left hi, dite_eq_left (show i.val < t + 1 + j ∧ l.val < t + 1 + j from ⟨hi', hl'⟩)]
      change g.val ⟨i.val, hi⟩ ⟨l.val, hl⟩ =
        (lowerBlockPair g x 1).val ((⟨i.val, hi⟩ : Fin (t + 1)).castAdd j)
          ((⟨l.val, hl⟩ : Fin (t + 1)).castAdd j)
      rw [lowerBlockPair_11]
    · rw [dite_eq_right hi]
      by_cases hi' : i.val < t + 1 + j
      · have hr : i.val < r := by omega
        have hx : i.val - (t + 1) < j := by omega
        have h₁ : (⟨i.val, hi'⟩ : Fin (t + 1 + j)) = (⟨i.val - (t + 1), hx⟩ : Fin j).natAdd (t + 1) :=
          Fin.ext (by change i.val = t + 1 + (i.val - (t + 1)); omega)
        rw [dite_eq_left hr, dite_eq_left (show i.val < t + 1 + j ∧ l.val < t + 1 + j from ⟨hi', hl'⟩)]
        change extendRows _ x _ _ = (lowerBlockPair g x 1).val ⟨i.val, hi'⟩
          ((⟨l.val, hl⟩ : Fin (t + 1)).castAdd j)
        rw [h₁, lowerBlockPair_21]
        change (if hX : i.val - (t + 1) < j then x ⟨i.val - (t + 1), hX⟩ else 0) ⟨l.val, hl⟩ = _
        rw [dite_eq_left hx]
      · have hne : i ≠ l := fun e => hi (e.symm ▸ hl)
        rw [dite_eq_right (show ¬ (i.val < t + 1 + j ∧ l.val < t + 1 + j) from fun p => hi' p.1), Matrix.one_apply_ne hne]
        by_cases hr : i.val < r
        · rw [dite_eq_left hr]
          have hx : ¬ i.val - (t + 1) < j := by omega
          change (if hX : i.val - (t + 1) < j then x ⟨i.val - (t + 1), hX⟩ else 0) ⟨l.val, hl⟩ = _
          rw [dite_eq_right hx]
          rfl
        · rw [dite_eq_right hr]
  · rw [dite_eq_right hl]
    by_cases hl' : l.val < t + 1 + j
    · by_cases hi' : i.val < t + 1 + j
      · have h₂ : (⟨l.val, hl'⟩ : Fin (t + 1 + j)) = (⟨l.val - (t + 1), by omega⟩ : Fin j).natAdd (t + 1) :=
          Fin.ext (by change l.val = t + 1 + (l.val - (t + 1)); omega)
        rw [dite_eq_left (show i.val < t + 1 + j ∧ l.val < t + 1 + j from ⟨hi', hl'⟩)]
        change (1 : M r) i l = (lowerBlockPair g x 1).val ⟨i.val, hi'⟩ ⟨l.val, hl'⟩
        rw [h₂]
        by_cases hi : i.val < t + 1
        · have hne : i ≠ l := fun e => hl (e ▸ hi)
          change (1 : M r) i l = (lowerBlockPair g x 1).val
            ((⟨i.val, hi⟩ : Fin (t + 1)).castAdd j) _
          rw [Matrix.one_apply_ne hne, lowerBlockPair_12]
        · have h₁ : (⟨i.val, hi'⟩ : Fin (t + 1 + j)) = (⟨i.val - (t + 1), by omega⟩ : Fin j).natAdd (t + 1) :=
            Fin.ext (by change i.val = t + 1 + (i.val - (t + 1)); omega)
          rw [h₁, lowerBlockPair_22]
          change (1 : M r) i l = (1 : Matrix (Fin j) (Fin j) ℝ) _ _
          simp only [Matrix.one_apply, Fin.ext_iff]
          have he : i.val - (t + 1) = l.val - (t + 1) ↔ i.val = l.val := by omega
          simp only [he]
      · rw [dite_eq_right (show ¬ (i.val < t + 1 + j ∧ l.val < t + 1 + j) from fun p => hi' p.1)]
    · rw [dite_eq_right (show ¬ (i.val < t + 1 + j ∧ l.val < t + 1 + j) from fun p => hl' p.2)]

/-- Extend the supplied column by zeros over the filled rectangle rows. -/
def extendColumn (j : ℕ) (y : Row t) : Fin (t + 1 + j) → ℝ :=
  fun i => if hi : i.val < t + 1 then y ⟨i.val, hi⟩ else 0

/-- The right upper-column action on a nonempty prefix reads the last filled row. -/
def RealRectangularRowActionStatement : Prop :=
  ∀ (r t j : ℕ) (h : t < r) (_hj : j < r - (t + 1)) (a : ℝˣ) (g : G t)
    (x : X (j + 1) t) (y : Row t),
    ∃ u : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ,
      point h g x * colUnip (extendColumn (j + 1) y) = u.val * point h g x ∧
      realWhittakerCharacter a u.val =
        (realScaledCharacter a).complex (∑ k, y k * x (Fin.last j) k)

theorem realRectangularRowAction : RealRectangularRowActionStatement := by
  intro r t j h hj a g x y
  let p := t + 1 + j
  let B := leadingBlock g x
  let z := B.val *ᵥ extendColumn (j + 1) y
  let U : Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ :=
    ⟨colUnip (r := r) z, colUnip_mem z⟩
  refine ⟨U, ?_, ?_⟩
  · rw [point_eq_pad h (by omega)]
    exact padGL_mul_colUnip _ B _
  · have hZ : realWhittakerCharacter a U.val = (realScaledCharacter a).complex (z (Fin.last p)) := by
      change realWhittakerCharacter a (colUnip (r := r) z) = _
      exact character_colUnip a z (show p + 1 < r + 1 by dsimp [p]; omega)
    rw [hZ]
    congr 1
    change (∑ k : Fin (t + 1 + (j + 1)), B.val (Fin.last p) k * extendColumn (j + 1) y k) = _
    rw [sum_castLE (show t + 1 ≤ t + 1 + (j + 1) by omega) _ (fun k hk => by simp [extendColumn, not_lt.mpr hk])]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hi : Fin.last p = (Fin.last j).natAdd (t + 1) := rfl
    change (lowerBlockPair g x 1).val (Fin.last p) (k.castAdd (j + 1)) *
      extendColumn (j + 1) y (k.castAdd (j + 1)) = _
    rw [hi, lowerBlockPair_21]
    have hy : extendColumn (j + 1) y (k.castAdd (j + 1)) = y k := dite_eq_left k.isLt
    rw [hy, mul_comm]

end Langlands.Global.RankinSelbergGlobal.RealRectangularRows
