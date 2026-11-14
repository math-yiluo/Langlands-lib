import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType

/-! # Statement: the scheme-theoretic centre of a reductive group over a base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A reductive group over an arbitrary scheme has a closed scheme-theoretic centre
of multiplicative type, and this representative remains the centre after every
base change (Conrad, Theorem 3.3.4). -/
def ReductiveRelativeCenterStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ (Z : GroupScheme S) (z : Z ⟶ G),
      IsSchemeTheoreticCenter z ∧
      RelativeMultiplicativeType.IsMultiplicativeType Z ∧
      ∀ (S' : Scheme.{u}) (b : S' ⟶ S),
        IsSchemeTheoreticCenter ((GroupScheme.baseChange b).map z)

end Langlands.GroupScheme
