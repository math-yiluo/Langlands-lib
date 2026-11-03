import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: parabolic subgroups are self-normalizing -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over a field `k`, every parabolic subgroup `j : P ⟶ G` of a connected reductive group `G`
is its own normalizer, as subgroup functors on all `k`-schemes. -/
def ParabolicSelfNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G), IsParabolicSubgroup j →
      (SubgroupFunctor.range j).normalizer = SubgroupFunctor.range j

end Langlands.GroupScheme
