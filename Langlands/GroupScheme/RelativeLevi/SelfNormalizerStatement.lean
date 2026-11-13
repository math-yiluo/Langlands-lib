import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Statement: Levi subgroups are their own normalizers -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Levi subgroups are self-normalizing** (Conrad, *Reductive group schemes* (2014),
Corollary 5.4.6, second assertion). For every scheme `S`, reductive group scheme `G` over
`S`, parabolic subgroup `i : P ⟶ G` and Levi subgroup `l : L ⟶ P`, the normalizer of the
image of `l` in `P`, as a subgroup functor on all `S`-schemes, is the image of `l`. -/
def RelativeLeviSelfNormalizerStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P L : GroupScheme S) (i : P ⟶ G) (l : L ⟶ P),
    IsReductive G → IsRelativeParabolicSubgroup i → IsRelativeLeviSubgroup l →
      (SubgroupFunctor.range l).normalizer = SubgroupFunctor.range l

end Langlands.GroupScheme
