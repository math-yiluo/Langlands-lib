import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Ring.Int.Units

/-! # Integral action on a rank-one difference line -/

noncomputable section

universe u

namespace Langlands.GroupScheme.IntegralRootLine

variable {M : Type u} [AddCommGroup M] [hM : Module.IsTorsionFree ℤ M]
  (a : M) (ha : a ≠ 0) (w : M ≃ₗ[ℤ] M)
  (hdiv : ∀ x : M, ∃ m : ℤ, x - w x = m • a)

omit hM in
private theorem apply_eq_smul :
    w a = (1 - Classical.choose (hdiv a)) • a := by
  calc
    w a = a - (a - w a) := (sub_sub_cancel _ _).symm
    _ = a - Classical.choose (hdiv a) • a :=
      congrArg (fun x : M => a - x) (Classical.choose_spec (hdiv a))
    _ = (1 - Classical.choose (hdiv a)) • a := by
      rw [sub_smul, one_smul]

omit hM in
private theorem symm_apply_eq_smul :
    w.symm a = (1 + Classical.choose (hdiv (w.symm a))) • a := by
  have h : w.symm a - a = Classical.choose (hdiv (w.symm a)) • a := by
    simpa only [w.apply_symm_apply] using Classical.choose_spec (hdiv (w.symm a))
  calc
    w.symm a = (w.symm a - a) + a := (sub_add_cancel _ _).symm
    _ = Classical.choose (hdiv (w.symm a)) • a + a :=
      congrArg (fun x : M => x + a) h
    _ = (1 + Classical.choose (hdiv (w.symm a))) • a := by
      rw [add_smul, one_smul, add_comm]

include hM ha in
private theorem coefficients_mul :
    (1 - Classical.choose (hdiv a)) *
        (1 + Classical.choose (hdiv (w.symm a))) = 1 := by
  apply smul_left_injective ℤ ha
  calc
    ((1 - Classical.choose (hdiv a)) *
        (1 + Classical.choose (hdiv (w.symm a)))) • a =
        (1 + Classical.choose (hdiv (w.symm a))) •
          ((1 - Classical.choose (hdiv a)) • a) := by
      rw [mul_comm, mul_smul]
    _ = (1 + Classical.choose (hdiv (w.symm a))) • w a :=
      congrArg
        (fun x : M => (1 + Classical.choose (hdiv (w.symm a))) • x)
        (apply_eq_smul a w hdiv).symm
    _ = w ((1 + Classical.choose (hdiv (w.symm a))) • a) :=
      (w.map_smul _ _).symm
    _ = w (w.symm a) := congrArg w (symm_apply_eq_smul a w hdiv).symm
    _ = (1 : ℤ) • a := by simp

/-- The actual integer unit by which an integral automorphism acts on its
nonzero rank-one difference line. -/
def lineUnit : ℤˣ :=
  Units.mkOfMulEqOne
    (1 - Classical.choose (hdiv a))
    (1 + Classical.choose (hdiv (w.symm a)))
    (coefficients_mul a ha w hdiv)

include hdiv in
theorem lineUnit_smul : (lineUnit a ha w hdiv : ℤ) • a = w a :=
  (apply_eq_smul a w hdiv).symm

include hM ha hdiv in
/-- Such an automorphism either fixes or negates the distinguished vector.
The vector need not be primitive. -/
theorem apply_eq_self_or_neg : w a = a ∨ w a = -a := by
  rcases Int.units_eq_one_or (lineUnit a ha w hdiv) with h | h
  · left
    simpa only [h, Units.val_one, one_smul] using
      (lineUnit_smul a ha w hdiv).symm
  · right
    simpa only [h, Units.val_neg, Units.val_one, neg_one_smul] using
      (lineUnit_smul a ha w hdiv).symm

include hM ha hdiv in
/-- Moving the distinguished vector forces the negative sign. -/
theorem apply_eq_neg_of_ne (hmove : w a ≠ a) : w a = -a :=
  (apply_eq_self_or_neg a ha w hdiv).resolve_left hmove

end Langlands.GroupScheme.IntegralRootLine
