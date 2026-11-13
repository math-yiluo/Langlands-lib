import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative

/-! # Statement: the unique Borel subgroup opposite to a Borel subgroup through a maximal torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Opposite Borel subgroups** (Conrad, *Reductive group schemes* (2014),
Proposition 5.2.12). Let `G` be a reductive group scheme over `S`, `t : T ⟶ G` a maximal
torus and `i : B ⟶ G` a Borel subgroup containing `T`. There is a Borel subgroup
`i' : B' ⟶ G` with `B' ∩ B = T`, and it is unique: every Borel subgroup `B''` with
`B'' ∩ B = T` has the same image as `B'`. Intersections and equalities are of images as
subgroup functors of `G`. -/
def RelativeOppositeBorelStatement : Prop :=
  ∀ (S : Scheme.{u}) (G B : GroupScheme S) (i : B ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G),
    IsReductive G →
    RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
    IsRelativeBorelSubgroup i → SubgroupFunctor.range t ≤ SubgroupFunctor.range i →
      ∃ (B' : GroupScheme S) (i' : B' ⟶ G), IsRelativeBorelSubgroup i' ∧
        SubgroupFunctor.range i' ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t ∧
        ∀ (B'' : GroupScheme S) (i'' : B'' ⟶ G), IsRelativeBorelSubgroup i'' →
          SubgroupFunctor.range i'' ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t →
            SubgroupFunctor.range i'' = SubgroupFunctor.range i'

end Langlands.GroupScheme
