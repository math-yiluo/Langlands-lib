import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: a group variety without unipotent subgroups is a torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Corollary 17.25, first sentence. A smooth connected affine group over an
algebraically closed field in which every smooth connected unipotent closed
subgroup is trivial is a torus. -/
def NoUnipotentSubgroupTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∀ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ G), IsClosedSubgroup u →
        Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
          SubgroupFunctor.range u = ⊥) →
      IsTorus G

end Langlands.GroupScheme
