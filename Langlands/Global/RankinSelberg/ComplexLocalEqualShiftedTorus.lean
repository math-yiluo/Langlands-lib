import Langlands.Global.RankinSelberg.ComplexLocalOrdinaryConvergence

/-! # The toral shift in the equal-rank unfolded kernel -/

noncomputable section

open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open scoped BigOperators

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ComplexLocalWhittakerGauge (logTorus logTorus_val)
open RealConvergenceAnalysis (rootPos exponent_le)

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "Y" => Fin m → ℝ
local notation "Z" => Fin n → ℝ
local notation "pad" => padGL (R := ℂ) (Nat.le_succ m)

/-- Pad the smaller logarithmic torus by zero in the last coordinate. -/
def padTorusLog (x : Y) : Z := fun j =>
  if hj : j.val < m then x ⟨j.val, hj⟩ else 0

@[simp] theorem padTorusLog_castSucc (x : Y) (i : Fin m) :
    padTorusLog x i.castSucc = x i := dite_eq_left i.isLt

@[simp] theorem padTorusLog_last (x : Y) : padTorusLog x (Fin.last m) = 0 :=
  dite_eq_right (Nat.lt_irrefl m)

theorem pad_logTorus (x : Y) : pad (logTorus x) = logTorus (padTorusLog x) := by
  apply Units.ext
  ext i j
  rw [Unfolding.padGL_apply, logTorus_val, logTorus_val]
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < m
    · simp only [hi, dite_true, Matrix.diagonal_apply_eq, padTorusLog]
    · simp only [hi, dite_false, Matrix.diagonal_apply_eq, padTorusLog, Real.exp_zero,
        Complex.ofReal_one, ite_true]
  · have hne : ∀ (hi : i.val < m) (hj : j.val < m),
        (⟨i.val, hi⟩ : Fin m) ≠ ⟨j.val, hj⟩ :=
      fun _ _ he => hij (Fin.ext (congrArg (fun j : Fin m => j.val) he))
    by_cases hi : i.val < m <;> by_cases hj : j.val < m <;>
      simp [hi, hj, hij, hne]

/-- The translation in the smaller torus removes the last large log coordinate from
the first `m` coordinates of the padded Iwasawa product. -/
def equalTorusShift (z : Z) : Y := fun i => z i.castSucc - z (Fin.last m)

theorem padTorusLog_add_eq_shifted (x : Y) (z : Z) :
    padTorusLog x + z = padTorusLog (x + equalTorusShift z) + fun _ => z (Fin.last m) := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Pi.add_apply, padTorusLog_last, zero_add]
  · simp only [Pi.add_apply, padTorusLog_castSucc, equalTorusShift]
    ring

theorem rootPos_add_const (z : Z) (c : ℝ) : rootPos (z + fun _ => c) = rootPos z := by
  simp only [rootPos, Pi.add_apply, add_sub_add_right_eq_sub]

theorem equalDeterminantLog_shifted (x : Y) (z : Z) (s : ℝ) :
    2 * (s - 1 / 2) * (∑ i, x i) + 2 * (s + (m : ℝ) / 2) * (∑ j, z j) =
      2 * (s - 1 / 2) * (∑ i, (x + equalTorusShift z) i) +
        (n : ℝ) * (∑ j, z j) + 2 * (n : ℝ) * (s - 1 / 2) * z (Fin.last m) := by
  simp only [Pi.add_apply, equalTorusShift, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Fin.sum_univ_castSucc z, Nat.cast_add, Nat.cast_one]
  ring

theorem exists_paddedTorus_decay (A : ℝ) (hA : 0 ≤ A) (t : ℝ) (ht : (A + 1) * (n : ℝ) ≤ t) :
    ∃ J : ℕ, ∀ x : Y,
      A * (∑ j, |x j|) - (J : ℝ) * rootPos (padTorusLog x) + t * (∑ j, x j) ≤
        -(∑ j, |x j|) := by
  let d : ℝ := ((m : ℕ) : ℝ) + 1
  have ht' : (A + 1) * d ≤ t := by simpa only [d, Nat.cast_add, Nat.cast_one] using ht
  obtain ⟨J, hJ⟩ := exists_nat_gt ((A + 1) * d + t * d)
  refine ⟨J, fun x => ?_⟩
  have h := exponent_le (t := t) (padTorusLog x) hA ht' hJ.le hJ.le
  have hx : (∑ j, |padTorusLog x j|) = ∑ j, |x j| := by
    rw [Fin.sum_univ_castSucc]
    simp
  have hy : (∑ j, padTorusLog x j) = ∑ j, x j := by
    rw [Fin.sum_univ_castSucc]
    simp
  rw [hx, hy, padTorusLog_last, max_self, mul_zero, sub_zero] at h
  linarith

/-- The shifted torus separates the determinant weight and admits an integrable
exponential envelope once the smaller spectral exponent is sufficiently large. -/
def ComplexLocalEqualShiftedTorusStatement : Prop :=
  (∀ (x : Y) (z : Z) (s : ℝ),
    2 * (s - 1 / 2) * (∑ i, x i) + 2 * (s + (m : ℝ) / 2) * (∑ j, z j) =
      2 * (s - 1 / 2) * (∑ i, (x + equalTorusShift z) i) +
        (n : ℝ) * (∑ j, z j) + 2 * (n : ℝ) * (s - 1 / 2) * z (Fin.last m)) ∧
  (∀ (A : ℝ), 0 ≤ A → ∀ t : ℝ, (A + 1) * (n : ℝ) ≤ t →
    ∃ J : ℕ, ∀ x : Y,
      A * (∑ j, |x j|) - (J : ℝ) * rootPos (padTorusLog x) + t * (∑ j, x j) ≤
        -(∑ j, |x j|))

theorem complexLocalEqualShiftedTorus : ComplexLocalEqualShiftedTorusStatement (r := r) :=
  ⟨equalDeterminantLog_shifted, exists_paddedTorus_decay⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
