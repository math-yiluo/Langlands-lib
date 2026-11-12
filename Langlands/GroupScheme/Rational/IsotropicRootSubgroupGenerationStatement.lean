import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.Rational.SplitTorus

/-!
# Root subgroups generate an isotropic almost-simple group

In an almost-simple group over a field that is not anisotropic, a closed subgroup containing a
maximal split torus and all relative root subgroups is the whole group.
This module states a proposition and supplies no proof of it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over any field `k`, let `G` be almost simple over `k` and not anisotropic, with maximal
split torus `i : S ⟶ G`. A closed subgroup `h : H ⟶ G` whose range contains the range of `i` and
every relative root subgroup `RelativeRoot.subgroup i a` has full range on every test scheme. -/
def IsotropicRootSubgroupGenerationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom], IsAlmostSimple G → ¬ IsAnisotropic G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G), IsClosedSubgroup h →
      SubgroupFunctor.range i ≤ SubgroupFunctor.range h →
      (∀ a ∈ relativeRoots i, RelativeRoot.subgroup i a ≤ SubgroupFunctor.range h) →
      SubgroupFunctor.range h = ⊤

end Langlands.GroupScheme
