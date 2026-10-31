import Langlands.AbelianScheme.Rational

/-! # Geometric relative dimension under rational isomorphism -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A genuine isomorphism in the rational category of abelian schemes preserves
each specified geometric relative dimension over an arbitrary base scheme.
This is a proposition target; no dimension-invariance theorem is assumed. -/
def RationalIsoRelativeDimensionStatement : Prop :=
  ∀ (S : Scheme.{u}) (B B' : AbelianScheme S),
    ((rationalization S).obj B ≅ (rationalization S).obj B') →
      ∀ g : ℕ, B.HasRelativeDimension g ↔ B'.HasRelativeDimension g

end Langlands.AbelianScheme
