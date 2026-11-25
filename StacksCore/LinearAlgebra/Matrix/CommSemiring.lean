module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-! # Linear algebra over commutative semirings

`Matrix.Nonsingular` and the resulting `StrongRankCondition` instance for nontrivial
commutative semirings used to live here; they are now in Mathlib, phrased via
`Matrix.IsDetpBalanced`. What remains are the `SubRegular` API and the permutation and
signed-part determinant lemmas that Mathlib does not carry, plus
`Matrix.nonsingular_iff_subRegular` relating the two formulations. -/

@[expose] public section

open Module Matrix Finset Equiv Perm

attribute [simp] isRegular_one

/-- `SubRegular p q` is the semiring-friendly version of "`p - q` is right-regular" (i.e. a
non-zero-divisor): the implication `a * p + b * q = b * p + a * q → a = b` for all `a, b`.
Over a ring this is equivalent to `IsRightRegular (p - q)`; in the symmetrized-semiring
literature (Plus 1990, Butkovič–Gaubert 1999) this corresponds to `p` and `q` being
"unbalanced" in the symmetrized semiring `R²`. -/
@[grind] def SubRegular {R : Type*} [Add R] [Mul R] (p q : R) : Prop :=
  ∀ {a b}, a * p + b * q = b * p + a * q → a = b

namespace SubRegular

/-- If `p` and `q` are sub-regular in a nontrivial semiring then `p ≠ q`. -/
@[grind ., simp] theorem ne {R : Type*} [NonAssocSemiring R] [Nontrivial R] {p q : R}
    (h : SubRegular p q) : p ≠ q :=
  fun heq ↦ one_ne_zero <| h <| by grind

/-- Sub-regularity is symmetric: `SubRegular p q → SubRegular q p`. -/
@[grind .] theorem symm {R : Type*} [AddCommMagma R] [Mul R] {p q : R} (h : SubRegular p q) :
    SubRegular q p := fun {a b} heq ↦ h <| by grind [add_comm]

/-- Sub-regularity is symmetric in `p` and `q`. -/
@[grind .] theorem comm {R : Type*} [AddCommMagma R] [Mul R] (p q : R) :
    SubRegular p q ↔ SubRegular q p := ⟨symm, symm⟩

end SubRegular

/-- Over a ring, sub-regularity of `(p, q)` reduces to sub-regularity of `(p - q, 0)`. -/
theorem subRegular_iff_sub {R : Type*} [NonUnitalNonAssocRing R] (p q : R) :
    SubRegular p q ↔ SubRegular (p - q) 0 := by
  simp [SubRegular, mul_sub, eq_sub_iff_add_eq, sub_add_eq_add_sub]
  grind

/-- `SubRegular p 0` is exactly `IsRightRegular p`. -/
@[simp] theorem subRegular_zero_right_iff_rightRegular {R : Type*} [NonUnitalNonAssocSemiring R]
    (p : R) : SubRegular p 0 ↔ IsRightRegular p := by
  simp [SubRegular, IsRightRegular, Function.Injective]

/-- `SubRegular 0 p` is exactly `IsRightRegular p`. -/
@[simp] theorem subRegular_zero_left_iff_rightRegular {R : Type*} [NonUnitalNonAssocSemiring R]
    (p : R) : SubRegular 0 p ↔ IsRightRegular p := by
  rw [SubRegular.comm, subRegular_zero_right_iff_rightRegular]

/-- Over a ring, `SubRegular p q` is exactly `IsRightRegular (p - q)`. -/
@[simp] theorem subRegular_iff_rightRegular_sub {R : Type*} [NonUnitalNonAssocRing R]
    (p q : R) : SubRegular p q ↔ IsRightRegular (p - q) := by
  rw [subRegular_iff_sub, subRegular_zero_right_iff_rightRegular]

namespace Equiv.Perm
variable {α : Type*} [Fintype α] [DecidableEq α]

end Equiv.Perm

namespace Matrix
variable {R : Type*} [CommSemiring R] {m n : Type*}

section detp
variable [Fintype n] [DecidableEq n]

end detp

end Matrix
