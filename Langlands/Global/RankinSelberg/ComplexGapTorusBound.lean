import Langlands.Global.RankinSelberg.ComplexUnequalOrdinaryFamily
import Langlands.Global.RankinSelberg.ComplexTwoBlockIwasawa
import Langlands.Global.RankinSelberg.RealConvergenceAnalysis

/-! # Exponential domination in the two-block complex torus -/

noncomputable section

open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapTorusBound

open ComplexTwoBlockHaar (blockLog)
open RealConvergenceAnalysis (rootPos rootPos_nonneg sub_last_le integrable_exp_neg_mul_sum_abs)

private theorem sum_blockLog {n k : ℕ} (hkn : k < n) (y : Fin k → ℝ) (z : Fin (n - k) → ℝ)
    (f : ℝ → ℝ) : (∑ i, f (blockLog hkn y z i)) = (∑ i, f (y i)) + (∑ j, f (z j)) := by
  have h := Fintype.sum_equiv (finCongr (Nat.add_sub_of_le hkn.le)).symm
    (fun i => f (blockLog hkn y z i)) (fun j => f (Fin.append y z j)) (fun _ => rfl)
  rw [h, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- The final ambient logarithmic coordinate belongs to the tail block. -/
theorem blockLog_last {r k : ℕ} (hkn : k < r + 1) (y : Fin k → ℝ) (z : Fin (r + 1 - k) → ℝ) :
    blockLog hkn y z (Fin.last r) = z ⟨r - k, by omega⟩ := by
  let j : Fin (r + 1 - k) := ⟨r - k, by omega⟩
  have hj : finCongr (Nat.add_sub_of_le hkn.le) (j.natAdd k) = Fin.last r := by
    apply Fin.ext
    change k + (r - k) = r
    omega
  rw [← hj]
  simp only [blockLog, Function.comp_apply, Equiv.symm_apply_apply, Fin.append_right, j]

private theorem sum_pos_le_last {r : ℕ} (x : Fin (r + 1) → ℝ) :
    (∑ i, max (x i) 0) ≤ ((r : ℝ) + 1) * (rootPos x + max (x (Fin.last r)) 0) := by
  calc
    _ ≤ ∑ _i : Fin (r + 1), (rootPos x + max (x (Fin.last r)) 0) := by
      refine Finset.sum_le_sum fun i _ => max_le ?_ ?_
      · have h₁ := sub_last_le x i
        have h₂ := le_max_left (x (Fin.last r)) 0
        linarith
      · exact add_nonneg (rootPos_nonneg x) (le_max_right _ _)
    _ = _ := by simp [nsmul_eq_mul, Nat.cast_add, mul_add]

private theorem sum_abs_eq_pos_add_neg {n : ℕ} (x : Fin n → ℝ) :
    (∑ i, |x i|) = (∑ i, max (x i) 0) + ∑ i, max (-x i) 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases le_total 0 (x i) with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero]
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_add]

/-- The first determinant power controls the negative first-block directions. Simple-root
and last-coordinate decay control the positive directions in both blocks. The negative tail
coordinates have their own decay factor. -/
theorem exponent_le {r k : ℕ} (hkn : k < r + 1) (y : Fin k → ℝ) (z : Fin (r + 1 - k) → ℝ)
    {A B T J P Q : ℝ} (hB : 0 ≤ B) (hT : A + 1 ≤ T)
    (hJ : max (2 * T) (B + 1) * ((r : ℝ) + 1) ≤ J)
    (hP : max (2 * T) (B + 1) * ((r : ℝ) + 1) ≤ P) (hQ : B + 1 ≤ Q) :
    let x := blockLog hkn y z
    A * (∑ i, |y i|) + B * (∑ i, |z i|) + T * (∑ i, y i) - J * rootPos x -
      P * max (x (Fin.last r)) 0 - Q * (∑ i, max (-z i) 0) ≤
        - ((∑ i, |y i|) + (∑ i, |z i|)) := by
  dsimp only
  let x := blockLog hkn y z
  let M := max (2 * T) (B + 1)
  have hM : 0 ≤ M := (by linarith : 0 ≤ B + 1).trans (le_max_right _ _)
  have h₁ := mul_le_mul_of_nonneg_right hT
    (show 0 ≤ ∑ i, |y i| from Finset.sum_nonneg fun i _ => abs_nonneg (y i))
  have h₂ := congrArg (T * ·) (ComplexUnequalFamily.sum_add_abs y)
  have h₃ := congrArg ((B + 1) * ·) (sum_abs_eq_pos_add_neg z)
  have h₄ : 2 * T * (∑ i, max (y i) 0) + (B + 1) * (∑ i, max (z i) 0) ≤
      M * (∑ i, max (x i) 0) := by
    rw [show (∑ i, max (x i) 0) = (∑ i, max (y i) 0) + (∑ i, max (z i) 0) from
      sum_blockLog hkn y z (fun w => max w 0), mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Finset.sum_nonneg fun _ _ => le_max_right _ _))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Finset.sum_nonneg fun _ _ => le_max_right _ _))
  have h₅ := mul_le_mul_of_nonneg_left (sum_pos_le_last x) hM
  have h₆ := mul_le_mul_of_nonneg_right hJ (rootPos_nonneg x)
  have h₇ := mul_le_mul_of_nonneg_right hP (le_max_right (x (Fin.last r)) 0)
  have h₈ := mul_le_mul_of_nonneg_right hQ
    (show 0 ≤ ∑ i, max (-z i) 0 from Finset.sum_nonneg fun i _ => le_max_right (-z i) 0)
  dsimp only [x] at h₄ h₅ h₆ h₇
  dsimp only [M] at h₄ h₅
  linarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]

private theorem sub_le_rootPos {r : ℕ} (x : Fin (r + 1) → ℝ)
    {i j : Fin (r + 1)} (hij : i ≤ j) : x i - x j ≤ rootPos x := by
  let y := fun i => x (min i j)
  have hRoot : rootPos y ≤ rootPos x := by
    unfold rootPos
    refine Finset.sum_le_sum fun a _ => ?_
    by_cases h : a.succ ≤ j
    · have h' : a.castSucc ≤ j := (Fin.le_def.mpr (Nat.le_succ a.val)).trans h
      rw [show y a.castSucc = x a.castSucc from congrArg x (min_eq_left h'),
        show y a.succ = x a.succ from congrArg x (min_eq_left h)]
    · have h' : j ≤ a.castSucc := by
        change ¬ a.val + 1 ≤ j.val at h
        change j.val ≤ a.val
        omega
      rw [show y a.castSucc = x j from congrArg x (min_eq_right h'),
        show y a.succ = x j from congrArg x (min_eq_right (le_of_not_ge h)), sub_self, max_self]
      exact le_max_right _ _
  have h := sub_last_le y i
  rw [show y i = x i from congrArg x (min_eq_left hij),
    show y (Fin.last r) = x j from congrArg x (min_eq_right (Fin.le_last j))] at h
  exact h.trans hRoot

private theorem sum_neg_le_first {r k : ℕ} (hkn : k < r + 1)
    (y : Fin k → ℝ) (z : Fin (r + 1 - k) → ℝ) :
    (∑ i, max (-z i) 0) ≤ (r + 1 - k : ℕ) *
      (rootPos (blockLog hkn y z) + max (-z ⟨0, Nat.sub_pos_of_lt hkn⟩) 0) := by
  let j : Fin (r + 1 - k) := ⟨0, Nat.sub_pos_of_lt hkn⟩
  let e := finCongr (Nat.add_sub_of_le hkn.le)
  let x := blockLog hkn y z
  have he (i : Fin (r + 1 - k)) : x (e (i.natAdd k)) = z i := by
    simp only [x, blockLog, Function.comp_apply, e, Equiv.symm_apply_apply, Fin.append_right]
  have h (i : Fin (r + 1 - k)) : z j - z i ≤ rootPos x := by
    rw [← he i, ← he j]
    apply sub_le_rootPos
    change k + 0 ≤ k + i.val
    omega
  calc
    _ ≤ ∑ _i : Fin (r + 1 - k), (rootPos x + max (-z j) 0) := by
      refine Finset.sum_le_sum fun i _ => max_le ?_ (add_nonneg (rootPos_nonneg x) (le_max_right _ _))
      have h₁ := h i
      have h₂ := le_max_left (-z j) 0
      linarith
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The negative tail directions can also be controlled by the first tail coordinate
and additional simple-root decay. -/
theorem exponent_le_first {r k : ℕ} (hkn : k < r + 1)
    (y : Fin k → ℝ) (z : Fin (r + 1 - k) → ℝ) {A B T J P Q : ℝ}
    (hB : 0 ≤ B) (hT : A + 1 ≤ T)
    (hJ : max (2 * T) (B + 1) * ((r : ℝ) + 1) + (B + 1) * (r + 1 - k : ℕ) ≤ J)
    (hP : max (2 * T) (B + 1) * ((r : ℝ) + 1) ≤ P)
    (hQ : (B + 1) * (r + 1 - k : ℕ) ≤ Q) :
    let x := blockLog hkn y z
    A * (∑ i, |y i|) + B * (∑ i, |z i|) + T * (∑ i, y i) - J * rootPos x -
      P * max (x (Fin.last r)) 0 - Q * max (-z ⟨0, Nat.sub_pos_of_lt hkn⟩) 0 ≤
        - ((∑ i, |y i|) + (∑ i, |z i|)) := by
  dsimp only
  let J₀ := max (2 * T) (B + 1) * ((r : ℝ) + 1)
  let x := blockLog hkn y z
  have h₁ := mul_le_mul_of_nonneg_left (sum_neg_le_first hkn y z) (by linarith : 0 ≤ B + 1)
  have h₂ := mul_le_mul_of_nonneg_right hJ (rootPos_nonneg x)
  have h₃ := mul_le_mul_of_nonneg_right hQ (le_max_right (-z ⟨0, Nat.sub_pos_of_lt hkn⟩) 0)
  have h₄ := exponent_le hkn y z hB hT (show J₀ ≤ J₀ from le_rfl) hP (Q := B + 1) le_rfl
  dsimp only [x] at h₂
  linarith only [h₁, h₂, h₃, h₄]

/-- The toral part of the gap majorant after absorbing the fixed exponential weights. -/
def torusEnvelope {r k : ℕ} (hkn : k < r + 1) (A B T J P Q : ℝ)
    (p : (Fin k → ℝ) × (Fin (r + 1 - k) → ℝ)) : ℝ :=
  let x := blockLog hkn p.1 p.2
  Real.exp (A * (∑ i, |p.1 i|) + B * (∑ i, |p.2 i|) + T * (∑ i, p.1 i) - J * rootPos x -
    P * max (x (Fin.last r)) 0 - Q * max (-p.2 ⟨0, Nat.sub_pos_of_lt hkn⟩) 0)

/-- For a sufficiently large first-block exponent, the envelope with sufficiently large
simple-root and Schwartz decay rates is integrable for product torus Lebesgue measure. -/
def ComplexGapTorusBoundStatement : Prop :=
  ∀ (r k : ℕ) (hkn : k < r + 1) (A B T J P Q : ℝ),
    0 ≤ B → A + 1 ≤ T →
    max (2 * T) (B + 1) * ((r : ℝ) + 1) + (B + 1) * (r + 1 - k : ℕ) ≤ J →
    max (2 * T) (B + 1) * ((r : ℝ) + 1) ≤ P → (B + 1) * (r + 1 - k : ℕ) ≤ Q →
    Integrable (torusEnvelope hkn A B T J P Q) (volume.prod volume)

theorem complexGapTorusBound : ComplexGapTorusBoundStatement := by
  intro r k hkn A B T J P Q hB hT hJ hP hQ
  have hOne : (0 : ℝ) < 1 := one_pos
  have hy := integrable_exp_neg_mul_sum_abs (n := k) hOne
  have hz := integrable_exp_neg_mul_sum_abs (n := r + 1 - k) hOne
  have hMajor := hy.mul_prod hz
  refine hMajor.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have hc : Continuous (torusEnvelope hkn A B T J P Q) := by
      unfold torusEnvelope rootPos blockLog
      fun_prop
    exact hc.aestronglyMeasurable
  · unfold torusEnvelope
    dsimp only
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply le_trans (Real.exp_le_exp.mpr (exponent_le_first hkn p.1 p.2 hB hT hJ hP hQ))
    exact le_of_eq (by simp only [neg_add, Real.exp_add, neg_mul, one_mul])

end Langlands.Global.RankinSelbergGlobal.ComplexGapTorusBound
