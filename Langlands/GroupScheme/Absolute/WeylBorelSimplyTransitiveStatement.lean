import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.InnerAutomorphism

/-! # Statement: the Weyl group acts simply transitively on the Borel subgroups through a
maximal torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Corollary 17.11 (last sentence) and Proposition 17.53. Let `j : T ⟶ G` be a
maximal torus of a smooth connected affine group over an algebraically closed field `k`, and
let `b : B ⟶ G` be a Borel subgroup containing `T`. Conjugation by `k`-points of `N_G(T)`:
* reaches every Borel subgroup containing `T`;
* fixes `B` for every `k`-point of `C_G(T)`;
* fixes `B` only for `k`-points of `C_G(T)`.
So `W(G,T)(k) = N_G(T)(k)/C_G(T)(k)` acts simply transitively on the Borel subgroups
containing `T`. -/
def WeylBorelSimplyTransitiveStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
    ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G), IsBorelSubgroup b →
      SubgroupFunctor.range j ≤ SubgroupFunctor.range b →
      (∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (b' : B' ⟶ G), IsBorelSubgroup b' →
        SubgroupFunctor.range j ≤ SubgroupFunctor.range b' →
          ∃ n ∈ normalizerPoints j,
            SubgroupFunctor.range (b ≫ (G.innerIso n).hom) = SubgroupFunctor.range b') ∧
      (∀ n ∈ centralizerPoints j,
        SubgroupFunctor.range (b ≫ (G.innerIso n).hom) = SubgroupFunctor.range b) ∧
      (∀ n ∈ normalizerPoints j,
        SubgroupFunctor.range (b ≫ (G.innerIso n).hom) = SubgroupFunctor.range b →
          n ∈ centralizerPoints j)

end Langlands.GroupScheme
