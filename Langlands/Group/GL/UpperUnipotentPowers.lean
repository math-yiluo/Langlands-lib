import Langlands.Group.GL.UpperUnipotentFactorizationProof
import Mathlib.Algebra.Ring.Semiconj
import Mathlib.Tactic.NoncommRing

/-! # Roots of upper-unipotent matrices -/

namespace Langlands.GeneralLinear

open UpperUnipotentFactorization (AgreeBelow StrictUpper agreeBelow_mul eq_of_agreeBelow
  mul_apply_eq_zero)

universe u

variable {n : ℕ} {F : Type u} [Field F]

local notation "Mat" => Matrix (Fin n) (Fin n) F

private theorem strictUpper_add {X Y : Mat} (hX : StrictUpper X) (hY : StrictUpper Y) :
    StrictUpper (X + Y) := by
  intro i j hij
  simp [Matrix.add_apply, hX i j hij, hY i j hij]

private theorem strictUpper_smul (a : F) {X : Mat} (hX : StrictUpper X) :
    StrictUpper (a • X) := by
  intro i j hij
  simp [hX i j hij]

private def powerRemainder (X : Mat) : ℕ → Mat
  | 0 => 0
  | k + 1 => powerRemainder X k + ((k : F) • X + powerRemainder X k) * X

private theorem one_add_pow_eq (X : Mat) (k : ℕ) :
    (1 + X) ^ k = 1 + ((k : F) • X + powerRemainder X k) := by
  induction k with
  | zero => simp [powerRemainder]
  | succ k ih =>
    rw [pow_succ, ih, powerRemainder, Nat.cast_succ, add_smul, one_smul]
    noncomm_ring

private theorem strictUpper_powerRemainder {X : Mat} (hX : StrictUpper X) (k : ℕ) :
    StrictUpper (powerRemainder X k) := by
  induction k with
  | zero => exact fun _ _ _ => rfl
  | succ k ih =>
    exact strictUpper_add ih (fun _ _ =>
      mul_apply_eq_zero (strictUpper_add (strictUpper_smul _ hX) ih) hX)

private theorem agreeBelow_powerRemainder {m : ℕ} {X Y : Mat}
    (hX : StrictUpper X) (hY : StrictUpper Y) (h : AgreeBelow m X Y) (k : ℕ) :
    AgreeBelow (m + 1) (powerRemainder X k) (powerRemainder Y k) := by
  induction k with
  | zero => exact fun _ _ _ => rfl
  | succ k ih =>
    have hmul := agreeBelow_mul
      (strictUpper_add (strictUpper_smul (k : F) hX) (strictUpper_powerRemainder hX k)) hX
      (strictUpper_add (strictUpper_smul (k : F) hY) (strictUpper_powerRemainder hY k)) hY
      (show AgreeBelow m ((k : F) • X + powerRemainder X k)
        ((k : F) • Y + powerRemainder Y k) from by
          intro i j hij
          simp only [Matrix.add_apply, Matrix.smul_apply, h i j hij, ih i j (by omega)]) h
    intro i j hij
    simp only [powerRemainder, Matrix.add_apply, ih i j hij, hmul i j hij]

private def rootStep (e : ℕ) (Z X : Mat) : Mat :=
  (e : F)⁻¹ • (Z - powerRemainder X e)

private theorem strictUpper_rootStep (e : ℕ) {Z X : Mat} (hZ : StrictUpper Z)
    (hX : StrictUpper X) : StrictUpper (rootStep e Z X) := by
  intro i j hij
  simp [rootStep, hZ i j hij, strictUpper_powerRemainder hX e i j hij]

private theorem strictUpper_rootIterate (e : ℕ) {Z X : Mat} (hZ : StrictUpper Z)
    (hX : StrictUpper X) (k : ℕ) : StrictUpper ((rootStep e Z)^[k] X) := by
  induction k with
  | zero => exact hX
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact strictUpper_rootStep e hZ ih

private theorem agreeBelow_rootIterate (e : ℕ) {Z X Y : Mat} (hZ : StrictUpper Z)
    (hX : StrictUpper X) (hY : StrictUpper Y) (k : ℕ) :
    AgreeBelow k ((rootStep e Z)^[k] X) ((rootStep e Z)^[k] Y) := by
  induction k with
  | zero =>
    intro i j hij
    have h : ¬ i < j := by
      change ¬ i.val < j.val
      omega
    exact (hX i j h).trans (hY i j h).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    intro i j hij
    simp only [rootStep, Matrix.smul_apply, Matrix.sub_apply,
      agreeBelow_powerRemainder (strictUpper_rootIterate e hZ hX k)
        (strictUpper_rootIterate e hZ hY k) ih e i j hij]

private def rootMatrix (e : ℕ) (U : Mat) : Mat :=
  1 + (rootStep e (U - 1))^[n] 0

private theorem rootMatrix_pow (e : ℕ) (he : (e : F) ≠ 0) {U : Mat}
    (hU : StrictUpper (U - 1)) : rootMatrix e U ^ e = U := by
  let Z := U - 1
  let X := (rootStep e Z)^[n] 0
  have h0 : StrictUpper (0 : Mat) := fun _ _ _ => rfl
  have hfix : rootStep e Z X = X := by
    change rootStep e Z ((rootStep e Z)^[n] 0) = (rootStep e Z)^[n] 0
    rw [← Function.iterate_succ_apply' (rootStep e Z) n 0, Function.iterate_succ_apply]
    exact eq_of_agreeBelow (agreeBelow_rootIterate e hU (strictUpper_rootStep e hU h0) h0 n)
  have hlinear : (e : F) • X = Z - powerRemainder X e := by
    calc
      (e : F) • X = (e : F) • rootStep e Z X :=
        congrArg (fun Y : Mat => (e : F) • Y) hfix.symm
      _ = Z - powerRemainder X e := by rw [rootStep, smul_smul, mul_inv_cancel₀ he, one_smul]
  change (1 + X) ^ e = U
  rw [one_add_pow_eq, hlinear, sub_add_cancel]
  dsimp [Z]
  abel

private theorem semiconjBy_smul_right {M X Y : Mat} (h : SemiconjBy M X Y) (a : F) :
    SemiconjBy M (a • X) (a • Y) := by
  change M * (a • X) = (a • Y) * M
  rw [Matrix.mul_smul, Matrix.smul_mul, h.eq]

private theorem semiconjBy_powerRemainder {M X Y : Mat} (h : SemiconjBy M X Y) (k : ℕ) :
    SemiconjBy M (powerRemainder X k) (powerRemainder Y k) := by
  induction k with
  | zero => simp [powerRemainder, SemiconjBy]
  | succ k ih =>
    exact ih.add_right (((semiconjBy_smul_right h (k : F)).add_right ih).mul_right h)

private theorem semiconjBy_rootMatrix (e : ℕ) {M U V : Mat} (h : SemiconjBy M U V) :
    SemiconjBy M (rootMatrix e U) (rootMatrix e V) := by
  have h1 : SemiconjBy M 1 1 := by simp [SemiconjBy]
  have hIter (k : ℕ) :
      SemiconjBy M ((rootStep e (U - 1))^[k] 0) ((rootStep e (V - 1))^[k] 0) := by
    induction k with
    | zero => simp [SemiconjBy]
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact semiconjBy_smul_right ((h.sub_right h1).sub_right (semiconjBy_powerRemainder ih e)) _
  exact h1.add_right (hIter n)

private theorem strictUpper_sub_one (u : upperUnipotent n F) :
    StrictUpper (u.val.val - 1) := by
  intro i j hij
  rcases eq_or_lt_of_le (not_lt.mp hij) with hji | hji
  · subst j
    simp
  · simp [u.property.1 hji, Matrix.one_apply_ne hji.ne']

/-- The upper-unipotent root obtained by solving the power equation along successive
superdiagonals. Its `e`-th power is the input when `e` is nonzero in the field. -/
noncomputable def upperUnipotentPowerRoot (e : ℕ) (u : upperUnipotent n F) :
    upperUnipotent n F := by
  let M := rootMatrix e u.val.val
  have h0 : StrictUpper (0 : Mat) := fun _ _ _ => rfl
  have hs := strictUpper_rootIterate e (strictUpper_sub_one u) h0 n
  have ht : M.IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    change ((1 + (rootStep e (u.val.val - 1))^[n] 0) : Mat) i j = 0
    rw [Matrix.add_apply, hs i j (not_lt_of_gt hji), Matrix.one_apply_ne hji.ne', add_zero]
  have hd (i : Fin n) : M i i = 1 := by
    simp [M, rootMatrix, hs i i (lt_irrefl i)]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular ht]
    simp only [hd, Finset.prod_const_one]
  exact ⟨Matrix.GeneralLinearGroup.mk'' M (hdet ▸ isUnit_one), ht, hd⟩

theorem upperUnipotentPowerRoot_pow (e : ℕ) (he : (e : F) ≠ 0) (u : upperUnipotent n F) :
    upperUnipotentPowerRoot e u ^ e = u := by
  apply Subtype.ext
  apply Units.ext
  change ((upperUnipotentPowerRoot e u).val ^ e).val = u.val.val
  rw [Units.val_pow_eq_pow_val]
  exact rootMatrix_pow e he (strictUpper_sub_one u)

theorem upperUnipotentPowerRoot_mul_eq_mul (e : ℕ) (a b : upperUnipotent n F)
    (m : Langlands.GeneralLinear n F) (h : a.val * m = m * b.val) :
    (upperUnipotentPowerRoot e a).val * m = m * (upperUnipotentPowerRoot e b).val := by
  apply Units.ext
  exact (semiconjBy_rootMatrix e (congrArg Units.val h).symm).eq.symm

end Langlands.GeneralLinear
