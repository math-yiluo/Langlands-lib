import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: actions of groups with connected fibres on reductive groups are inner -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Actions with connected fibres are inner** (Conrad, *Reductive group schemes* (2014),
Proposition 7.2.6). Let `G` be a reductive group scheme over a scheme `S` and `H` a group
scheme over `S` whose residue fibres are connected. Let `p : G ⟶ G_ad` be an fppf quotient of
`G` by its centre and `c` an action of `G_ad` on `G` by group automorphisms whose restriction
along `p` is conjugation of `G` on itself (the natural action of `G/Z_G` on `G`). Then every
action `a` of `H` on `G` by group automorphisms is the restriction of `c` along a unique
homomorphism `H ⟶ G_ad`. -/
def ReductiveConnectedActionInnerStatement : Prop :=
  ∀ (S : Scheme.{u}) (G H : GroupScheme S), IsReductive G →
    (∀ s : S,
      ConnectedSpace ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj H).X.left) →
    ∀ (Gad : GroupScheme S) (p : G ⟶ Gad), RelativeRoot.IsFppfQuotient (center G) p →
    ∀ c : AutomorphicAction Gad G, c.restrict p = AutomorphicAction.conjugation (𝟙 G) →
    ∀ a : AutomorphicAction H G, ∃! φ : H ⟶ Gad, c.restrict φ = a

end Langlands.GroupScheme
