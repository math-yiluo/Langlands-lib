import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.Basic

/-! # Finite étaleness of the roots-of-unity coordinate algebra -/

universe u

namespace Langlands.GroupScheme

/-- The actual polynomial quotient for roots of unity is finite and étale over
its coefficient ring when its positive index is a unit.
This proposition is a statement target, not a proof. -/
def MuCoordinateAlgebraStatement : Prop :=
  ∀ (A : CommRingCat.{u}) (n : ℕ),
    0 < n → IsUnit (n : A) →
      Module.Finite A (AdjoinRoot ((Polynomial.X : Polynomial A) ^ n - 1)) ∧
        Algebra.Etale A (AdjoinRoot ((Polynomial.X : Polynomial A) ^ n - 1))

end Langlands.GroupScheme
