import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Statement: subgroups containing a Borel subgroup are connected and self-normalizing -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Theorem 17.48 and Corollary 17.49. Let `G` be a smooth connected affine group over
a field `k`, and let `i : P ⟶ G` be a smooth closed subgroup through which a geometric Borel
subgroup `j : B ⟶ G` factors. Then `P` is connected and equals its all-test normalizer
`N_G(P)`. Taking `P = B` gives the normalizer theorem `N_G(B) = B`. -/
def BorelContainingSubgroupSelfNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (P B : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G) (j : B ⟶ G) (f : B ⟶ P),
    IsClosedSubgroup i → Smooth P.X.hom → IsGeometricBorelSubgroup j → f ≫ i = j →
      ConnectedSpace P.X.left ∧
        (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i

end Langlands.GroupScheme
