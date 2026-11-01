import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Normal finitely generated integer subalgebras -/

universe u

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Every finite subset of an integrally closed domain is contained in a
finitely generated integer subalgebra that is integrally closed and noetherian. -/
def NormalFiniteTypeSubalgebraStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (s : Finset R),
    ∃ T : Subalgebra ℤ R, T.FG ∧ (↑s : Set R) ⊆ T ∧
      IsIntegrallyClosed ↥T ∧ IsNoetherianRing ↥T

end Langlands.AlgebraicGeometry.NoetherianApproximation
