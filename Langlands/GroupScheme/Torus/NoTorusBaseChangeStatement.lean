import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.SubgroupFunctor

/-! # Statement: absence of tori is invariant under field extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Proposition 17.81 with Corollaries 14.9 and 14.18, in homomorphism form: if every
homomorphism from a torus over `k` to a smooth affine group scheme `Q` over `k` is trivial on all
points, then for every field extension `K` of `k`, every homomorphism from a torus over `K` to
the base change `Q_K` is trivial on all points. -/
def NoTorusBaseChangeStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom],
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ g : T.toGrp ⟶ Q, SubgroupFunctor.range g = ⊥) →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of K))), IsTorus T.toGrp →
      ∀ g : T.toGrp ⟶ (GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj Q,
        SubgroupFunctor.range g = ⊥

end Langlands.GroupScheme
