import Langlands.GroupScheme.Cartan.Basic
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Statement: normalizers of subgroups containing a Cartan subgroup -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Lemma 17.47. Let `G` be a smooth connected affine group over a field `k` and let
`h : H ⟶ G` be a smooth closed subgroup containing a Cartan subgroup of `G`. Every closed
subgroup `n : N ⟶ G` representing the all-test normalizer of `H` is smooth, and `H` is open
in `N`; equivalently `N_G(H)° = H°`. -/
def CartanContainingNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
    IsClosedSubgroup h → Smooth H.X.hom →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G), IsCartanSubgroup c →
      SubgroupFunctor.range c ≤ SubgroupFunctor.range h →
    ∀ (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
      (SubgroupFunctor.range h).normalizer.IsRepresentedBy n → IsClosedSubgroup n →
        Smooth N.X.hom ∧ ∀ f : H ⟶ N, f ≫ n = h → IsOpenImmersion f.hom.hom.left

end Langlands.GroupScheme
