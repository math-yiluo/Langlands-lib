import Langlands.Representation.Archimedean.RealOrthogonalUncertainty

/-! # Finite propagation of adjacent compact rotation modes -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealRotationFinitePropagation

open Polynomial Complex RealOrthogonalUncertainty
open RealOrthogonalUncertainty.IsModeDecomposition

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
  {a b c : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}

/-- All modes of `v` lie strictly inside the indicated symmetric interval. -/
def HasModeBound (π : ℤ → Module.End ℂ W) (n : ℕ) (v : W) : Prop :=
  ∀ m : ℤ, (n : ℤ) ≤ |m| → π m v = 0

theorem mode_bound_step
    (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S)
    {n : ℕ} {v : W} (hv : HasModeBound π n v) :
    HasModeBound π (n + 1) (b v) := by
  intro m hm
  have hp := hM.proj_apply_of_lie (lie_raise hab hca) m v
  have hn := hM.proj_apply_of_lie (lie_lower hab hca) m v
  have ht1 : |m| ≤ |m - 1| + 1 := by
    simpa only [sub_add_cancel, abs_one] using abs_add_le (m - 1) (1 : ℤ)
  have ht2 : |m| ≤ |m - (-1)| + 1 := by
    simpa only [sub_add_cancel, abs_neg, abs_one] using abs_add_le (m - (-1)) (-1 : ℤ)
  have hm1 : (n : ℤ) ≤ |m - 1| := by omega
  have hm2 : (n : ℤ) ≤ |m - (-1)| := by omega
  calc
    π m (b v) =
        (1 / 2 : ℂ) • (π m ((b - I • c) v) + π m ((b + I • c) v)) := by
      conv_lhs => rw [eq_half_raise_add_lower (b := b) (c := c)]
      rw [LinearMap.smul_apply, map_smul, LinearMap.add_apply, map_add]
    _ = 0 := by
      rw [hp, hn, hv (m - 1) hm1, hv (m - (-1)) hm2,
        map_zero, map_zero, add_zero, smul_zero]

theorem mode_bound_pow
    (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S)
    {n : ℕ} {v : W} (hv : HasModeBound π n v) (d : ℕ) :
    HasModeBound π (n + d) ((b ^ d) v) := by
  induction d with
  | zero => simpa using hv
  | succ d ih =>
      simpa only [pow_succ', Module.End.mul_apply, Nat.add_assoc] using
        mode_bound_step hab hca hM ih

/-- A degree-`d` polynomial in the adjacent generator increases the mode bound by at most `d`. -/
theorem mode_bound_aeval
    (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S)
    {n : ℕ} {v : W} (hv : HasModeBound π n v) (Q : ℂ[X]) :
    HasModeBound π (n + Q.natDegree) (aeval b Q v) := by
  intro m hm
  rw [aeval_eq_sum_range, LinearMap.sum_apply, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hmi : ((n + i : ℕ) : ℤ) ≤ |m| := by omega
  rw [LinearMap.smul_apply, map_smul, mode_bound_pow hab hca hM hv i m hmi, smul_zero]

end Langlands.Archimedean.RealRotationFinitePropagation

namespace Langlands.Archimedean

open Polynomial RealOrthogonalUncertainty RealRotationFinitePropagation in
/-- Polynomial operators in an adjacent rotation have the stated finite mode propagation. -/
def RealRotationFinitePropagationStatement : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
    (a b c : Module.End ℂ W) (π : ℤ → Module.End ℂ W) (S : Finset ℤ),
    a * b - b * a = c → c * a - a * c = b →
    IsModeDecomposition a π S →
    ∀ (n : ℕ) (v : W), HasModeBound π n v →
    ∀ Q : ℂ[X], HasModeBound π (n + Q.natDegree) (aeval b Q v)

theorem realRotationFinitePropagation : RealRotationFinitePropagationStatement := by
  intro W _ _ a b c π S hab hca hM n v hv Q
  exact RealRotationFinitePropagation.mode_bound_aeval hab hca hM hv Q

end Langlands.Archimedean
