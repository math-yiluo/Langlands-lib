import Mathlib.Algebra.CharP.Frobenius
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.FiniteType

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Every iterate of Frobenius on a finite type integer algebra is a finite ring map. -/
def FiniteIterateFrobeniusStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R]
    (p n : ℕ) [ExpChar R p], (iterateFrobenius R p n).Finite

end Langlands.AlgebraicGeometry.NoetherianApproximation
