import Langlands.AbelianScheme.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Divisibility of geometric points of abelian schemes -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- At an algebraically closed geometric point, every actual point of an abelian
scheme is divisible by any natural number that is nonzero in the point field.
This is a statement target, not a proof. -/
def AlgClosedPointDivisibilityStatement : Prop :=
  ∀ (S : Scheme.{u}) (B : AbelianScheme S) (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) (m : ℕ), (m : K) ≠ 0 →
      ∀ y : Over.mk s ⟶ B.X, ∃ x : Over.mk s ⟶ B.X, x ^ m = y

end Langlands.AbelianScheme
