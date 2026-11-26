import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Instances.Matrix

/-! # Polynomial lower bound for small orthogonal Haar balls -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.OrthogonalHaar

local notation "O" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ

variable {n : ℕ}

/-- Squared Frobenius distance in the real matrix embedding of the orthogonal group. -/
def distSq (x y : O n) : ℝ :=
  Matrix.trace (star ((x : M n) - (y : M n)) * ((x : M n) - (y : M n)))

theorem distSq_eq_sum (x y : O n) :
    distSq x y = ∑ j, ∑ i, ((x : M n) i j - (y : M n) i j) ^ 2 := by
  simp only [distSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply,
    star_trivial, Matrix.sub_apply, pow_two]

theorem distSq_mul_left (g x y : O n) : distSq (g * x) (g * y) = distSq x y := by
  let A : M n := (x : M n) - (y : M n)
  change Matrix.trace (star ((g : M n) * (x : M n) - (g : M n) * (y : M n)) *
    ((g : M n) * (x : M n) - (g : M n) * (y : M n))) = Matrix.trace (star A * A)
  rw [← mul_sub]
  change Matrix.trace (star ((g : M n) * A) * ((g : M n) * A)) = Matrix.trace (star A * A)
  rw [star_mul, mul_assoc, ← mul_assoc (star (g : M n)), Unitary.star_mul_self_of_mem g.prop,
    one_mul]

private theorem abs_entry_le_one (x : O n) (i j : Fin n) : |(x : M n) i j| ≤ 1 := by
  have h := congrArg (fun A : M n => A j j) (Unitary.star_mul_self_of_mem x.prop)
  have hsum : ∑ a, ((x : M n) a j) ^ 2 = 1 := by
    simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply_eq, pow_two]
      using h
  have hle : ((x : M n) i j) ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun a _ => sq_nonneg ((x : M n) a j)) (Finset.mem_univ i)
  rw [← abs_one]
  exact sq_le_sq.mp (by simpa only [one_pow] using hle)

private def gridIndex (m : ℕ) (x : O n) (i j : Fin n) : Fin (2 * m + 1) :=
  ⟨⌊(m : ℝ) * ((x : M n) i j + 1)⌋₊, by
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_of_le
    have hx := (abs_le.mp (abs_entry_le_one x i j)).2
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg m : 0 ≤ (m : ℝ))]⟩

private theorem distSq_le_of_gridIndex_eq (m : ℕ) (hm : 0 < m)
    {x y : O n} (h : gridIndex m x = gridIndex m y) :
    distSq x y ≤ ((n : ℝ) / m) ^ 2 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [distSq_eq_sum]
  calc
    _ ≤ ∑ _ : Fin n, ∑ _ : Fin n, (1 / (m : ℝ)) ^ 2 := by
      refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => ?_
      let a := (m : ℝ) * ((x : M n) i j + 1)
      let b := (m : ℝ) * ((y : M n) i j + 1)
      have ha : 0 ≤ a := mul_nonneg hmR.le (by linarith [(abs_le.mp (abs_entry_le_one x i j)).1])
      have hb : 0 ≤ b := mul_nonneg hmR.le (by linarith [(abs_le.mp (abs_entry_le_one y i j)).1])
      have he : ⌊a⌋₊ = ⌊b⌋₊ := congrArg (fun q => (q i j).val) h
      have ha₁ := Nat.floor_le ha
      have hb₁ := Nat.floor_le hb
      have ha₂ := Nat.lt_floor_add_one a
      have hb₂ := Nat.lt_floor_add_one b
      rw [he] at ha₁ ha₂
      have hdiff : |(m : ℝ) * ((x : M n) i j - (y : M n) i j)| ≤ 1 := by
        rw [abs_le]
        constructor <;> dsimp [a, b] at ha₁ ha₂ hb₁ hb₂ <;> linarith only [ha₁, ha₂, hb₁, hb₂]
      have habs : |(x : M n) i j - (y : M n) i j| ≤ 1 / (m : ℝ) := by
        rw [abs_mul, abs_of_pos hmR, mul_comm] at hdiff
        exact (le_div_iff₀ hmR).mpr hdiff
      apply sq_le_sq.mpr
      simpa only [abs_of_nonneg (div_nonneg zero_le_one hmR.le)] using habs
    _ = ((n : ℝ) / m) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Normalized Haar measure gives a polynomial lower bound on the ball of Frobenius
radius `n / m` at the identity. The exponent is the ambient matrix dimension. -/
def OrthogonalHaarSmallBallStatement : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (O n)] [MeasurableMul (O n)]
    (μ : Measure (O n)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (m : ℕ), 0 < m →
      1 / ((2 * m + 1 : ℕ) : ℝ) ^ (n * n) ≤
        μ.real {x : O n | distSq x 1 ≤ ((n : ℝ) / m) ^ 2}

/-- Partition the entry cube into a finite grid, then cover the orthogonal group by a
left translate of the ball for each grid cell. -/
theorem orthogonalHaarSmallBall : OrthogonalHaarSmallBallStatement := by
  intro n _ _ μ _ _ m hm
  classical
  let Q := Fin n → Fin n → Fin (2 * m + 1)
  let B : Set (O n) := {x | distSq x 1 ≤ ((n : ℝ) / m) ^ 2}
  let g (q : Q) : O n := if h : ∃ x, gridIndex m x = q then h.choose else 1
  let U (q : Q) : Set (O n) := (fun x => (g q)⁻¹ * x) ⁻¹' B
  have hcover : (univ : Set (O n)) ⊆ ⋃ q, U q := by
    intro x _
    let q : Q := gridIndex m x
    have hg : gridIndex m (g q) = q := by
      have h : ∃ y, gridIndex m y = q := ⟨x, rfl⟩
      dsimp only [g]
      rw [dite_eq_left h]
      exact h.choose_spec
    refine mem_iUnion.mpr ⟨q, ?_⟩
    change distSq ((g q)⁻¹ * x) 1 ≤ _
    have hdist := distSq_mul_left (g q) ((g q)⁻¹ * x) 1
    rw [mul_inv_cancel_left, mul_one] at hdist
    rw [← hdist]
    exact distSq_le_of_gridIndex_eq m hm hg.symm
  have hcount : Fintype.card Q = (2 * m + 1) ^ (n * n) := by
    simp only [Q, Fintype.card_fun, Fintype.card_fin, ← pow_mul]
  have hbound : (1 : ℝ≥0∞) ≤ ((2 * m + 1 : ℕ) : ℝ≥0∞) ^ (n * n) * μ B := by
    calc
      1 = μ (univ : Set (O n)) := measure_univ.symm
      _ ≤ μ (⋃ q, U q) := measure_mono hcover
      _ ≤ ∑ q, μ (U q) := measure_iUnion_fintype_le μ U
      _ = _ := by
        simp only [U, measure_preimage_mul, Finset.sum_const, Finset.card_univ, hcount,
          nsmul_eq_mul, Nat.cast_pow]
  have hreal := ENNReal.toReal_mono (by finiteness) hbound
  rw [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at hreal
  change 1 / ((2 * m + 1 : ℕ) : ℝ) ^ (n * n) ≤ (μ B).toReal
  apply (div_le_iff₀ (by positivity)).mpr
  rw [mul_comm]
  exact hreal

end Langlands.Archimedean.OrthogonalHaar
