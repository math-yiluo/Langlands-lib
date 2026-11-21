import Langlands.Global.RankinSelberg.ComplexLocalWhittakerGauge
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Schwartz decay along the complex last row -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexLastRowSchwartz

open Langlands.Archimedean
open Langlands.RankinSelberg (lastRow)
open ComplexLocalWhittakerGauge (logTorus logTorus_val)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear r.succ ℂ
local notation "K" => unitaryCompact ℂ r.succ
local notation "Vec" => Fin r.succ → ℂ

private theorem lastRow_logTorus_mul (y : Fin r.succ → ℝ) (k : K) :
    Langlands.RankinSelberg.lastRow (logTorus y * k.val) =
      Real.exp (y (Fin.last r)) • Langlands.RankinSelberg.lastRow k.val := by
  funext j
  change ((logTorus y * k.val).val) (Fin.last r) j =
    Real.exp (y (Fin.last r)) • k.val.val (Fin.last r) j
  rw [Units.val_mul, logTorus_val, Matrix.diagonal_mul, Complex.real_smul]

private theorem one_le_mul_norm_unitary_lastRow (k : K) :
    1 ≤ (r.succ : ℝ) * ‖Langlands.RankinSelberg.lastRow k.val‖ := by
  let v := Langlands.RankinSelberg.lastRow k.val
  have hv (j : Fin r.succ) : ‖v j‖ ≤ 1 :=
    LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup k.2 _ _
  have hn : ‖v‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 hv
  have hsum : (∑ j, ‖v j‖ ^ 2) = (1 : ℝ) := by
    have hu : k.val.val * star k.val.val = 1 := Unitary.mul_star_self_of_mem k.2
    have h := congrArg (fun M : Matrix (Fin r.succ) (Fin r.succ) ℂ => M (Fin.last r) (Fin.last r)) hu
    have hEntry (j : Fin r.succ) : ((‖v j‖ ^ 2 : ℝ) : ℂ) = v j * star (v j) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self, Complex.star_def, mul_comm]
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_one]
    simp_rw [hEntry]
    simpa only [v, Langlands.RankinSelberg.lastRow, Matrix.mul_apply, Matrix.star_apply,
      Matrix.one_apply_eq] using h
  calc
    1 = ∑ j, ‖v j‖ ^ 2 := hsum.symm
    _ ≤ ∑ _j : Fin r.succ, ‖v‖ ^ 2 := Finset.sum_le_sum fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v j) _
    _ = (r.succ : ℝ) * ‖v‖ ^ 2 := by simp [nsmul_eq_mul]
    _ ≤ (r.succ : ℝ) * ‖v‖ := by
      exact mul_le_mul_of_nonneg_left
        (by rw [pow_two]; exact mul_le_of_le_one_right (norm_nonneg _) hn) (by positivity)

private theorem exp_le_mul_norm_lastRow (y : Fin r.succ → ℝ) (k : K) :
    Real.exp (max (y (Fin.last r)) 0) ≤
      (r.succ : ℝ) * (1 + ‖Langlands.RankinSelberg.lastRow (logTorus y * k.val)‖) := by
  have h₁ : (1 : ℝ) ≤ r.succ := by exact_mod_cast Nat.succ_pos r
  rw [lastRow_logTorus_mul, norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  rcases le_total 0 (y (Fin.last r)) with h | h
  · rw [max_eq_left h]
    have hh := mul_le_mul_of_nonneg_left (one_le_mul_norm_unitary_lastRow k)
      (Real.exp_nonneg (y (Fin.last r)))
    nlinarith only [hh, h₁]
  · rw [max_eq_right h, Real.exp_zero]
    exact h₁.trans (le_mul_of_one_le_right (by positivity)
      (le_add_of_nonneg_right (by positivity)))

/-- A bound for the Schwartz test in the last logarithmic coordinate, expressed
through finitely many order-zero Schwartz seminorms. -/
def lastRowTestBound (q : ℕ) (Φ : 𝓢(Vec, ℂ)) : ℝ :=
  (r.succ : ℝ) ^ q * (2 ^ q *
    ((Finset.Iic (q, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ)

theorem continuous_lastRowTestBound (q : ℕ) : Continuous (lastRowTestBound (r := r) q) := by
  refine ((Seminorm.continuous_finsetSup fun m _ => ?_).const_mul _).const_mul _
  exact (schwartz_withSeminorms ℝ Vec ℂ).continuous_seminorm m

@[simp]
theorem lastRowTestBound_zero (q : ℕ) : lastRowTestBound (r := r) q 0 = 0 := by
  simp [lastRowTestBound]

theorem lastRowTestBound_nonneg (q : ℕ) (Φ : 𝓢(Vec, ℂ)) : 0 ≤ lastRowTestBound q Φ := by
  unfold lastRowTestBound
  positivity

/-- A Schwartz test on the complex last row has arbitrary exponential decay in the
positive part of its last logarithmic diagonal coordinate. -/
def ComplexLastRowSchwartzStatement : Prop :=
  ∀ (Φ : 𝓢(Vec, ℂ)) (q : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin r.succ → ℝ) (k : K),
    ‖Φ (Langlands.RankinSelberg.lastRow (logTorus y * k.val))‖ ≤
      C * Real.exp (-(q : ℝ) * max (y (Fin.last r)) 0)

theorem norm_lastRow_le_testBound (Φ : 𝓢(Vec, ℂ)) (q : ℕ) (y : Fin r.succ → ℝ) (k : K) :
    ‖Φ (Langlands.RankinSelberg.lastRow (logTorus y * k.val))‖ ≤
      lastRowTestBound q Φ * Real.exp (-(q : ℝ) * max (y (Fin.last r)) 0) := by
  let C := 2 ^ q * ((Finset.Iic (q, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ
  let v := Langlands.RankinSelberg.lastRow (logTorus y * k.val)
  let m := max (y (Fin.last r)) 0
  have hΦ : (1 + ‖v‖) ^ q * ‖Φ v‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (q, 0)) le_rfl le_rfl Φ v
  have hv : Real.exp m ^ q ≤ ((r.succ : ℝ) * (1 + ‖v‖)) ^ q :=
    pow_le_pow_left₀ (Real.exp_nonneg _) (exp_le_mul_norm_lastRow y k) _
  have h : Real.exp ((q : ℝ) * m) * ‖Φ v‖ ≤ (r.succ : ℝ) ^ q * C := by
    rw [Real.exp_nat_mul]
    calc
      _ ≤ ((r.succ : ℝ) * (1 + ‖v‖)) ^ q * ‖Φ v‖ :=
        mul_le_mul_of_nonneg_right hv (norm_nonneg _)
      _ = (r.succ : ℝ) ^ q * ((1 + ‖v‖) ^ q * ‖Φ v‖) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left hΦ (by positivity)
  change ‖Φ v‖ ≤ (r.succ : ℝ) ^ q * C * Real.exp (-(q : ℝ) * m)
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using h)

theorem complexLastRowSchwartz : ComplexLastRowSchwartzStatement (r := r) :=
  fun Φ q => ⟨lastRowTestBound q Φ, lastRowTestBound_nonneg q Φ, norm_lastRow_le_testBound Φ q⟩

end Langlands.Global.RankinSelbergGlobal.ComplexLastRowSchwartz
