import Langlands.GroupScheme.Rational.Characters

/-! # Points whose commutators are central

A group scheme `G` over `S` has *trivial second centre* when every point `g` over a test
scheme `T`, all of whose commutators with points of `G` (after every base change of `T`)
lie in the scheme-theoretic centre, is itself central. -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- Every point whose commutators with all points, after every base change, are central is
itself central. -/
def SecondCenterTrivial (G : GroupScheme S) : Prop :=
  ∀ (T : Over S) (g : T ⟶ G.X),
    (∀ (T' : Over S) (a : T' ⟶ T) (h : T' ⟶ G.X), (a ≫ g) * h * (a ≫ g)⁻¹ * h⁻¹ ∈ (center G).carrier T') →
      g ∈ (center G).carrier T

end Langlands.GroupScheme
