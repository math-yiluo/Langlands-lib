import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative

/-! # Statement: quasi-split inner forms of reductive group schemes over any base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Existence of quasi-split inner forms over any base** (Conrad, *Reductive group schemes*
(2014), p.258 and Proposition 7.2.11). Let `G` be a reductive group scheme over a scheme `S`,
`p : G ⟶ G_ad` an fppf quotient of `G` by its centre and `c` the action of `G_ad` on `G` whose
restriction along `p` is conjugation. Then `G` has an inner form `G'` that is quasi-split and
has a Borel subgroup `B'` containing a maximal torus `T'` of `G'`. Here `G'` is an inner form
of `G` if, on some étale surjective `U ⟶ S`, there is an isomorphism of `G` and `G'` over the
points of `U` whose discrepancy on every pair of points of `U` is the action of a point of
`G_ad`. -/
def RelativeQuasiSplitInnerFormExistenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∀ (Gad : GroupScheme S) (p : G ⟶ Gad), RelativeRoot.IsFppfQuotient (center G) p →
    ∀ c : AutomorphicAction Gad G, c.restrict p = AutomorphicAction.conjugation (𝟙 G) →
    ∃ G' : GroupScheme S,
      (∃ U : Over S, Etale U.hom ∧ Surjective U.hom ∧
        ∃ e : LocalGroupIso G G' U, e.HasInnerDiscrepancy c) ∧
      IsRelativeQuasiSplit G' ∧
      ∃ (B' : GroupScheme S) (i : B' ⟶ G') (T' : CommGroupScheme S) (t : T'.toGrp ⟶ G'),
        IsRelativeBorelSubgroup i ∧ RelativeTorus.IsTorus T'.toGrp ∧ IsClosedSubgroup t ∧
        IsFibrewiseMaximalTorus t ∧ SubgroupFunctor.range t ≤ SubgroupFunctor.range i

end Langlands.GroupScheme
