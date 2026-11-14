import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: groups of multiplicative type embed in tori -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Groups of multiplicative type are closed subgroups of tori** (Conrad, *Reductive group
schemes* (2014), Proposition B.3.8). For every group `H` of multiplicative type over a scheme
`S` there is an `S`-torus `T` and a homomorphism `H ⟶ T` that is a closed immersion. -/
def MultiplicativeTypeTorusEmbeddingStatement : Prop :=
  ∀ (S : Scheme.{u}) (H : GroupScheme S),
    RelativeMultiplicativeType.IsMultiplicativeType H →
    ∃ (T : GroupScheme S) (i : H ⟶ T), RelativeTorus.IsTorus T ∧ IsClosedSubgroup i

end Langlands.GroupScheme
