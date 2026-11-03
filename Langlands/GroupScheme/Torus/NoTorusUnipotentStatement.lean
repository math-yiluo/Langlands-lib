import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.SubgroupFunctor
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: a connected group variety without tori is unipotent -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Proposition 17.81, for smooth affine groups and in homomorphism form: a smooth
connected affine group scheme `Q` over a field `k` such that every homomorphism from a torus
over `k` to `Q` is trivial on all points is unipotent. -/
def NoTorusUnipotentStatement : Prop :=
  ∀ (k : Type u) [Field k] (Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left],
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
      ∀ g : T.toGrp ⟶ Q, SubgroupFunctor.range g = ⊥) →
    IsUnipotent Q

end Langlands.GroupScheme
