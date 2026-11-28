import Langlands.GroupTheory.CocycleExtension
import Mathlib.Algebra.Group.Commutator

/-! # Commutators in normalized cocycle extensions -/

open scoped commutatorElement

namespace Langlands.NormalizedTwoCocycle.Extension

universe u v

variable {G : Type u} {A : Type v} [CommGroup G] [CommGroup A] [MulDistribMulAction G A]

/-- For a trivial action, the commutator of any two lifts is the inclusion of the
quotient of the cocycle values in the two orders. -/
theorem commutator_eq_inl_div (c : NormalizedTwoCocycle G A)
    (htriv : ∀ (g : G) (a : A), g • a = a) (x z : c.Extension) :
    ⁅x, z⁆ = inl c (c (x.right, z.right) / c (z.right, x.right)) := by
  have hmul : x * z = inl c (c (x.right, z.right) / c (z.right, x.right)) * (z * x) := by
    apply Extension.ext
    · simp only [mul_left, inl_left, inl_right, htriv, c.one_left, mul_one]
      calc
        _ = x.left * z.left *
            ((c (x.right, z.right) / c (z.right, x.right)) * c (z.right, x.right)) := by
              rw [div_mul_cancel]
        _ = _ := by ac_rfl
    · simp only [mul_right, inl_right, one_mul, mul_comm x.right z.right]
  calc
    ⁅x, z⁆ = (x * z) * (z * x)⁻¹ := by
      rw [commutatorElement_def, mul_inv_rev, mul_assoc (x * z)]
    _ = _ := by rw [hmul, mul_inv_cancel_right]

end Langlands.NormalizedTwoCocycle.Extension
