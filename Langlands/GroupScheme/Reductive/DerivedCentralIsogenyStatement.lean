import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Statement: central isogenies from the derived group and the maximal central torus -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Central isogenies attached to the derived group** (Conrad, *Reductive group schemes*
(2014), Corollary 5.3.3). Let `G` be a reductive group scheme over a scheme `S`. Call
`z : Z ⟶ G` a maximal central torus when it is a closed, central subgroup, `Z` is an `S`-torus,
and every closed central subgroup `z' : Z' ⟶ G` with `Z'` an `S`-torus has range contained in the
range of `z`. Then
1. `G` has a maximal central torus;
2. for every closed subgroup `d : D ⟶ G` with normal range and `D` semisimple (reductive with
   semisimple geometric fibres), every fppf quotient `q : G ⟶ Q` by the range of `d` with `Q` an
   `S`-torus, and every maximal central torus `z`, the multiplication map `Z × D ⟶ G`,
   `(x, y) ↦ z(x) d(y)`, is a central isogeny, and for every fppf quotient `p : G ⟶ P` by the
   range of `z` the homomorphism `(q, p) : G ⟶ Q × P` is a central isogeny.

By Theorem 5.3.1 (`RelativeDerivedGroupStatement`) the subgroups `d` in item 2 are exactly the
closed embeddings with range the derived group `D(G)`, and `Q` is the maximal torus quotient
`G/D(G)`. -/
def ReductiveDerivedCentralIsogenyStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    let IsMaximalCentralTorus : ∀ {Z : GroupScheme S}, (Z ⟶ G) → Prop :=
      fun {Z} z => IsClosedSubgroup z ∧ IsCentral z ∧ RelativeTorus.IsTorus Z ∧
        ∀ (Z' : GroupScheme S) (z' : Z' ⟶ G), IsClosedSubgroup z' → IsCentral z' →
          RelativeTorus.IsTorus Z' → SubgroupFunctor.range z' ≤ SubgroupFunctor.range z
    (∃ (Z : GroupScheme S) (z : Z ⟶ G), IsMaximalCentralTorus z) ∧
    ∀ (D : GroupScheme S) (d : D ⟶ G), IsClosedSubgroup d →
      (SubgroupFunctor.range d).IsNormal → IsReductive D →
      (∀ s : S, IsSemisimple (geometricFiber D s)) →
      ∀ (Q : GroupScheme S) (q : G ⟶ Q), RelativeTorus.IsTorus Q →
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q →
      ∀ (Z : GroupScheme S) (z : Z ⟶ G) (hz : IsCentral z), IsMaximalCentralTorus z →
        IsCentralIsogeny (prodHom z d (hz.commute_values d)) ∧
        ∀ (P : GroupScheme S) (p : G ⟶ P),
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) p →
          IsCentralIsogeny (CartesianMonoidalCategory.lift q p)

end Langlands.GroupScheme
