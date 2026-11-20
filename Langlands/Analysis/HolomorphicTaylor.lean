import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Order

/-! # The formal Taylor series of a scalar holomorphic function -/

noncomputable section

namespace Langlands.Analysis

/-- The ring of scalar functions that are holomorphic near the indicated point. -/
def holomorphicAtSubring (z : ℂ) : Subring (ℂ → ℂ) where
  carrier := {f | AnalyticAt ℂ f z}
  one_mem' := analyticAt_const
  mul_mem' hf hg := AnalyticAt.mul hf hg
  zero_mem' := analyticAt_const
  add_mem' hf hg := AnalyticAt.add hf hg
  neg_mem' hf := AnalyticAt.neg hf

/-- Taylor coefficients normalized by factorials give a ring homomorphism
from functions holomorphic at `z` to formal power series. -/
def holomorphicTaylor (z : ℂ) : holomorphicAtSubring z →+* PowerSeries ℂ where
  toFun f := PowerSeries.mk fun n => iteratedDeriv n f.val z / (n.factorial : ℂ)
  map_zero' := by
    ext n
    simp only [PowerSeries.coeff_mk, Subring.coe_zero, iteratedDeriv_const_zero, zero_div, map_zero]
  map_one' := by
    ext n
    rw [PowerSeries.coeff_mk, Subring.coe_one, PowerSeries.coeff_one]
    cases n with
    | zero => simp [iteratedDeriv_zero]
    | succ n => simp [Pi.one_def, iteratedDeriv_const]
  map_add' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add, Subring.coe_add]
    rw [iteratedDeriv_add f.property.contDiffAt g.property.contDiffAt, add_div]
  map_mul' f g := by
    ext n
    rw [PowerSeries.coeff_mk, Subring.coe_mul, PowerSeries.coeff_mul,
      iteratedDeriv_mul f.property.contDiffAt g.property.contDiffAt,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [PowerSeries.coeff_mk, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.cast_choose ℂ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h₁ : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h₂ : ((n - i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp

@[simp]
theorem coeff_holomorphicTaylor (z : ℂ) (f : holomorphicAtSubring z) (n : ℕ) :
    PowerSeries.coeff n (holomorphicTaylor z f) = iteratedDeriv n f.val z / (n.factorial : ℂ) :=
  PowerSeries.coeff_mk n (fun k => iteratedDeriv k f.val z / (k.factorial : ℂ))

@[simp]
theorem constantCoeff_holomorphicTaylor (z : ℂ) (f : holomorphicAtSubring z) :
    PowerSeries.constantCoeff (holomorphicTaylor z f) = f.val z := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_holomorphicTaylor]
  simp

/-- A holomorphic function of finite analytic order has a nonzero Taylor series. -/
theorem holomorphicTaylor_ne_zero (z : ℂ) (f : holomorphicAtSubring z)
    (hf : analyticOrderAt f.val z ≠ ⊤) : holomorphicTaylor z f ≠ 0 := by
  let n := (analyticOrderAt f.val z).toNat
  have hn : analyticOrderAt f.val z = n := (ENat.natCast_toNat_eq_self.mpr hf).symm
  have hderiv := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero f.property).mp hn).2
  intro hzero
  have hcoeff := congrArg (PowerSeries.coeff n) hzero
  rw [coeff_holomorphicTaylor, map_zero] at hcoeff
  exact hderiv ((div_eq_zero_iff.mp hcoeff).resolve_right
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))

end Langlands.Analysis
