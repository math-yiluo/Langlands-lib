import Mathlib.RingTheory.RingHom.FiniteType
import Mathlib.RingTheory.Unramified.Basic
import Langlands.AlgebraicGeometry.Picard.GeometricallyUnibranchDomain

/-! # Local algebra for a birational unramified morphism -/

universe u

namespace Langlands.AlgebraicGeometry

/-- A finite type unramified subalgebra of a geometrically unibranch local
 domain's fraction field equals the base if its closed fibre is nonempty. -/
def LocalUnramifiedBirationalAlgebraStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R],
    GeometricallyUnibranchDomain R →
    ∀ (A : Subalgebra R (FractionRing R)) [Algebra.FiniteType R A]
      [Algebra.FormallyUnramified R A] (q : Ideal A) [q.IsPrime]
      [q.LiesOver (IsLocalRing.maximalIdeal R)], A = ⊥

end Langlands.AlgebraicGeometry
