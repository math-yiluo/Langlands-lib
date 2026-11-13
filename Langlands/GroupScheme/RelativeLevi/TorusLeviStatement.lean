import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative

/-! # Statement: the Levi subgroup containing a maximal torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **A maximal torus lies in exactly one Levi subgroup** (Conrad, *Reductive group
schemes* (2014), Proposition 5.4.5). For every scheme `S`, reductive group scheme `G` over
`S`, parabolic subgroup `i : P ⟶ G` and closed torus `t : T ⟶ P` that is a maximal torus on
every residue fibre of `P`, there is a Levi subgroup `l : L ⟶ P` whose image contains that
of `t`, and every Levi subgroup of `P` whose image contains that of `t` has the same image
as `l` on every test scheme. -/
def RelativeTorusLeviStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P : GroupScheme S) (i : P ⟶ G) (T : CommGroupScheme S)
    (t : T.toGrp ⟶ P),
    IsReductive G → IsRelativeParabolicSubgroup i →
    RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
      ∃ (L : GroupScheme S) (l : L ⟶ P), IsRelativeLeviSubgroup l ∧
        SubgroupFunctor.range t ≤ SubgroupFunctor.range l ∧
        ∀ (L' : GroupScheme S) (l' : L' ⟶ P), IsRelativeLeviSubgroup l' →
          SubgroupFunctor.range t ≤ SubgroupFunctor.range l' →
            SubgroupFunctor.range l' = SubgroupFunctor.range l

end Langlands.GroupScheme
