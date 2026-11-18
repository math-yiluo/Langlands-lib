import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Perfect

/-! # One-variable rational pole removal from a unit-circle bound -/

noncomputable section

open Polynomial

namespace Langlands.Plancherel

namespace UnitCirclePoleRemoval

/-- A polynomial fraction bound outside finitely many circle points extends
to the corresponding numerator-denominator norm inequality on the whole
circle. Zeros of the denominator may be omitted from the bound. -/
theorem polynomial_norm_le_mul_of_div_bound
    (p q : Polynomial ℂ) (hq : q ≠ 0) (E : Set Circle) (hE : E.Finite) (C : ℝ)
    (hbound : ∀ z : Circle, z ∉ E → q.eval (z : ℂ) ≠ 0 →
      ‖p.eval (z : ℂ) / q.eval (z : ℂ)‖ ≤ C) (z : Circle) :
    ‖p.eval (z : ℂ)‖ ≤ C * ‖q.eval (z : ℂ)‖ := by
  let : Nontrivial Circle := ⟨⟨-1, 1, Circle.neg_ne_self 1⟩⟩
  let : ∀ w : Circle, Filter.NeBot (nhdsWithin w {w}ᶜ) :=
    fun w => PerfectSpace.not_isolated w
  have hroots : Set.Finite {w : Circle | q.eval (w : ℂ) = 0} := by
    exact (Polynomial.finite_setOfPred_isRoot hq).preimage
      Circle.coe_injective.injOn
  have hdense : Dense ((Set.univ : Set Circle) \
      (E ∪ {w : Circle | q.eval (w : ℂ) = 0})) :=
    dense_univ.sdiff_finite (hE.union hroots)
  have hpcont : Continuous (fun w : Circle => ‖p.eval (w : ℂ)‖) :=
    (p.continuous.comp continuous_subtype_val).norm
  have hqcont : Continuous (fun w : Circle => C * ‖q.eval (w : ℂ)‖) :=
    continuous_const.mul (q.continuous.comp continuous_subtype_val).norm
  apply (closure_minimal (t := {w : Circle |
    ‖p.eval (w : ℂ)‖ ≤ C * ‖q.eval (w : ℂ)‖}) ?_ (isClosed_le hpcont hqcont))
      (hdense z)
  intro w hw
  have hwE : w ∉ E := fun he => hw.2 (Or.inl he)
  have hwq : q.eval (w : ℂ) ≠ 0 := fun he => hw.2 (Or.inr he)
  have hb := hbound w hwE hwq
  rw [norm_div] at hb
  exact (div_le_iff₀ (norm_pos_iff.mpr hwq)).mp hb

/-- A reduced polynomial fraction bounded on the unit circle outside a
finite exceptional set has no unit-circle zero of its denominator. -/
theorem denominator_eval_ne_zero_of_coprime_div_bound
    (p q : Polynomial ℂ) (hq : q ≠ 0) (hcop : IsCoprime p q)
    (E : Set Circle) (hE : E.Finite) (C : ℝ)
    (hbound : ∀ z : Circle, z ∉ E → q.eval (z : ℂ) ≠ 0 →
      ‖p.eval (z : ℂ) / q.eval (z : ℂ)‖ ≤ C) (z : Circle) :
    q.eval (z : ℂ) ≠ 0 := by
  intro hqz
  have hb := polynomial_norm_le_mul_of_div_bound p q hq E hE C hbound z
  rw [hqz, norm_zero, mul_zero] at hb
  have hpz : p.eval (z : ℂ) = 0 := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  obtain ⟨a, b, hab⟩ := hcop
  have he := congrArg (Polynomial.eval (z : ℂ)) hab
  simp only [eval_add, eval_mul, eval_one, hpz, hqz, mul_zero, add_zero] at he
  exact zero_ne_one he

end UnitCirclePoleRemoval

/-- A one-variable complex rational function is regular on the unit circle
when its reduced denominator is nonzero at every point of the circle. -/
def RatFuncUnitCircleRegular (r : RatFunc ℂ) : Prop :=
  ∀ z : Circle, r.denom.eval (z : ℂ) ≠ 0

/-- Bounded evaluations outside any finite exceptional set remove all
unit-circle poles of a complex rational function. The bound need only be
known where the reduced denominator is nonzero. -/
theorem ratFuncUnitCircleRegular_of_bound
    (r : RatFunc ℂ) (E : Set Circle) (hE : E.Finite) (C : ℝ)
    (hbound : ∀ z : Circle, z ∉ E → r.denom.eval (z : ℂ) ≠ 0 →
      ‖r.eval (RingHom.id ℂ) (z : ℂ)‖ ≤ C) :
    RatFuncUnitCircleRegular r := by
  apply UnitCirclePoleRemoval.denominator_eval_ne_zero_of_coprime_div_bound
    r.num r.denom r.denom_ne_zero r.isCoprime_num_denom E hE C
  intro z hz hd
  simpa only [RatFunc.eval, Polynomial.eval₂_id] using hbound z hz hd

/-- In particular it suffices to know the bound away from the prescribed
finite exceptional set, without a separate denominator condition. -/
theorem ratFuncUnitCircleRegular_of_bound_off_finite
    (r : RatFunc ℂ) (E : Set Circle) (hE : E.Finite) (C : ℝ)
    (hbound : ∀ z : Circle, z ∉ E → ‖r.eval (RingHom.id ℂ) (z : ℂ)‖ ≤ C) :
    RatFuncUnitCircleRegular r :=
  ratFuncUnitCircleRegular_of_bound r E hE C (fun z hz _ => hbound z hz)

end Langlands.Plancherel
