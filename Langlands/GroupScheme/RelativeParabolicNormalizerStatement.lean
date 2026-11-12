import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: parabolic subgroups of reductive group schemes are self-normalizing -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Parabolic subgroups are self-normalizing over any ring** (Conrad, *Reductive group
schemes* (2014), Corollary 5.2.8, first assertion). Over every commutative ring `R`, let `G` be
a reductive group scheme and `i : P ⟶ G` a smooth closed subgroup whose base change to every
field is parabolic. Then the normalizer of `P` in `G`, as a subgroup functor on all
`R`-schemes, is `P`. -/
def RelativeParabolicSelfNormalizerStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G P : GroupScheme (Spec (CommRingCat.of R))) (i : P ⟶ G),
    IsReductive G → Smooth P.X.hom → IsClosedSubgroup i →
    (∀ (k : Type u) [Field k] [Algebra R k],
      IsParabolicSubgroup ((GroupScheme.baseChange (Spec.algebraMap R k)).map i)) →
    (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i

end Langlands.GroupScheme
