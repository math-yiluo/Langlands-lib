import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-! # Rational points of geometrically reduced algebras over separably closed fields

This module states that a nonzero finitely generated geometrically reduced algebra over a
separably closed field has a rational point (Stacks, Tags 056V and 056U).
It supplies no proof.
-/

universe u v

namespace Langlands.CommutativeAlgebra

/-- Every nonzero finitely generated geometrically reduced algebra over a separably closed
field `k` admits a `k`-algebra homomorphism to `k`. -/
def SeparablyClosedRationalPointStatement : Prop :=
  ∀ (k : Type u) (R : Type v) [Field k] [IsSepClosed k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] [Nontrivial R] [Algebra.IsGeometricallyReduced k R],
    Nonempty (R →ₐ[k] k)

end Langlands.CommutativeAlgebra
