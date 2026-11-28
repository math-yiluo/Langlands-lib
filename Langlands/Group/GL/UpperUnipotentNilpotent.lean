import Langlands.Group.GL.UpperUnipotentPowers
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Group

/-! # Nilpotence and unique powers in the upper-unipotent group -/

namespace Langlands.GeneralLinear

open UpperUnipotentFactorization (AgreeBelow StrictUpper agreeBelow_mul eq_of_agreeBelow)
open scoped commutatorElement

universe u

section Ring

variable {n : ℕ} {R : Type u} [CommRing R]

local notation "Mat" => Matrix (Fin n) (Fin n) R

private abbrev strictPart (a : upperUnipotent n R) : Mat :=
  a.val.val - 1

private theorem strictUpper_strictPart (a : upperUnipotent n R) :
    StrictUpper (strictPart a) := by
  intro i j hij
  rcases eq_or_lt_of_le (not_lt.mp hij) with hji | hji
  · subst j
    simp [strictPart]
  · simp [strictPart, a.property.1 hji, Matrix.one_apply_ne hji.ne']

private theorem strictPart_one : strictPart (1 : upperUnipotent n R) = 0 := by
  change (1 : Mat) - 1 = 0
  exact sub_self _

private theorem strictPart_mul (a b : upperUnipotent n R) :
    strictPart (a * b) = strictPart a + strictPart b + strictPart a * strictPart b := by
  change a.val.val * b.val.val - 1 =
    (a.val.val - 1) + (b.val.val - 1) + (a.val.val - 1) * (b.val.val - 1)
  noncomm_ring

private theorem strictPart_injective :
    Function.Injective (strictPart : upperUnipotent n R → Mat) := by
  intro a b h
  apply Subtype.ext
  apply Units.ext
  exact sub_left_inj.mp h

private theorem agreeBelow_mul_right {m : ℕ} {a b : upperUnipotent n R}
    (h : AgreeBelow m (strictPart a) (strictPart b)) (g : upperUnipotent n R) :
    AgreeBelow m (strictPart (a * g)) (strictPart (b * g)) := by
  have hp := agreeBelow_mul (strictUpper_strictPart a) (strictUpper_strictPart g)
    (strictUpper_strictPart b) (strictUpper_strictPart g) h (fun _ _ _ => rfl)
  intro i j hij
  simp only [strictPart_mul, Matrix.add_apply, h i j hij, hp i j (by omega)]

private theorem agreeBelow_commutator {m : ℕ} {a : upperUnipotent n R}
    (h : AgreeBelow m (strictPart a) 0) (b : upperUnipotent n R) :
    AgreeBelow (m + 1) (strictPart ⁅a, b⁆) 0 := by
  have hz : StrictUpper (0 : Mat) := fun _ _ _ => rfl
  have hab := agreeBelow_mul (strictUpper_strictPart a) (strictUpper_strictPart b)
    hz (strictUpper_strictPart b) h (fun _ _ _ => rfl)
  have hba := agreeBelow_mul (strictUpper_strictPart b) (strictUpper_strictPart a)
    (strictUpper_strictPart b) hz (fun _ _ _ => rfl) h
  simp only [zero_mul] at hab
  simp only [mul_zero] at hba
  have hswap : AgreeBelow (m + 1) (strictPart (a * b)) (strictPart (b * a)) := by
    intro i j hij
    simp only [strictPart_mul, Matrix.add_apply, hab i j hij, hba i j hij,
      Matrix.zero_apply, add_zero]
    exact add_comm _ _
  have hr := agreeBelow_mul_right hswap (a⁻¹ * b⁻¹)
  rw [show (a * b) * (a⁻¹ * b⁻¹) = ⁅a, b⁆ by simp [commutatorElement_def, mul_assoc],
    show (b * a) * (a⁻¹ * b⁻¹) = 1 by group, strictPart_one] at hr
  exact hr

private theorem mem_upperCentralSeries_of_agreeBelow (k : ℕ) (a : upperUnipotent n R)
    (h : AgreeBelow (n - k) (strictPart a) 0) :
    a ∈ Subgroup.upperCentralSeries (upperUnipotent n R) k := by
  induction k generalizing a with
  | zero =>
    rw [Nat.sub_zero] at h
    rw [show a = 1 from strictPart_injective ((eq_of_agreeBelow h).trans strictPart_one.symm)]
    exact Subgroup.one_mem _
  | succ k ih =>
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro b
    apply ih
    intro i j hij
    exact agreeBelow_commutator h b i j (by omega)

/-- Strict upper superdiagonals give a central series of length at most the matrix size. -/
theorem upperUnipotent_isNilpotent (n : ℕ) (R : Type u) [CommRing R] :
    Group.IsNilpotent (upperUnipotent n R) := by
  refine ⟨n, eq_top_iff.mpr fun a _ => mem_upperCentralSeries_of_agreeBelow n a ?_⟩
  rw [Nat.sub_self]
  intro i j hij
  apply strictUpper_strictPart
  change ¬ i.val < j.val
  omega

end Ring

section Field

variable {n : ℕ} {F : Type u} [Field F]

private theorem agreeBelow_pow_difference {m : ℕ} {a b : upperUnipotent n F}
    (h : AgreeBelow m (strictPart a) (strictPart b)) (e : ℕ) :
    AgreeBelow (m + 1) (strictPart (a ^ e) - strictPart (b ^ e))
      ((e : F) • (strictPart a - strictPart b)) := by
  induction e with
  | zero => simp [AgreeBelow, strictPart_one]
  | succ e ih =>
    have hp : AgreeBelow m (strictPart (a ^ e)) (strictPart (b ^ e)) := by
      intro i j hij
      apply sub_eq_zero.mp
      calc
        (strictPart (a ^ e) - strictPart (b ^ e)) i j =
            ((e : F) • (strictPart a - strictPart b)) i j := ih i j (by omega)
        _ = 0 := by rw [Matrix.smul_apply, Matrix.sub_apply, h i j hij, sub_self, smul_zero]
    have hmul := agreeBelow_mul (strictUpper_strictPart (a ^ e)) (strictUpper_strictPart a)
      (strictUpper_strictPart (b ^ e)) (strictUpper_strictPart b) hp h
    intro i j hij
    have hlinear := ih i j hij
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hlinear
    simp only [pow_succ, strictPart_mul, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, hmul i j hij, Nat.cast_succ, add_mul, one_mul, ← hlinear]
    abel

/-- An exponent nonzero in the field has at most one root in the upper-unipotent group. -/
theorem upperUnipotent_pow_injective (e : ℕ) (he : (e : F) ≠ 0) :
    Function.Injective (fun a : upperUnipotent n F => a ^ e) := by
  intro a b hab
  apply strictPart_injective
  apply eq_of_agreeBelow
  have hstep (m : ℕ) : AgreeBelow m (strictPart a) (strictPart b) := by
    induction m with
    | zero =>
      intro i j hij
      have hz : ¬ i < j := by
        change ¬ i.val < j.val
        omega
      rw [strictUpper_strictPart a i j hz, strictUpper_strictPart b i j hz]
    | succ m ih =>
      intro i j hij
      have h := agreeBelow_pow_difference ih e i j hij
      simp only [hab, sub_self, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at h
      exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left he)
  exact hstep n

/-- The power permutation of the upper-unipotent group, with the superdiagonal root
as its inverse. -/
noncomputable def upperUnipotentPowerEquiv (e : ℕ) (he : (e : F) ≠ 0) :
    upperUnipotent n F ≃ upperUnipotent n F where
  toFun a := a ^ e
  invFun := upperUnipotentPowerRoot e
  left_inv a := upperUnipotent_pow_injective e he (upperUnipotentPowerRoot_pow e he (a ^ e))
  right_inv := upperUnipotentPowerRoot_pow e he

end Field
end Langlands.GeneralLinear
