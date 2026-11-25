module

public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# A flat algebra preserves nonzerodivisors

For a flat `A`-algebra `B`, a nonzerodivisor of `A` maps to a nonzerodivisor of `B`: flatness makes
multiplication by it regular on `B`. This is the algebra-level reading of Mathlib's
`Module.Flat.isSMulRegular_of_nonZeroDivisors`.
-/

@[expose] public section

open scoped nonZeroDivisors

/-- A flat algebra carries the nonzerodivisors of the base ring to nonzerodivisors. -/
theorem algebraMap_mem_nonZeroDivisors_of_flat {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Flat A B] {a : A} (ha : a ∈ A⁰) : algebraMap A B a ∈ B⁰ := by
  have hreg : IsSMulRegular B a :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (R := A) (M := B) ha
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  exact hreg (by simpa [Algebra.smul_def, mul_comm] using hb)
