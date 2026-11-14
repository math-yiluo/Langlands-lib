import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.Lattice

/-! # Statement: the unipotent radical of the centralizer of a torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Corollary 17.57. Let `G` be a smooth connected affine group over an algebraically
closed field `k`, let `s : S ⟶ G` be a closed torus and let `c : C ⟶ G` be a closed subgroup
representing the centralizer `C_G(S)`. If `u : U ⟶ G` is the unipotent radical of `G` and
`v : V ⟶ C` is the unipotent radical of `C`, then `R_u(C_G(S)) = R_u(G) ∩ C_G(S)` as
all-test subgroup functors of `G`. -/
def TorusCentralizerUnipotentRadicalStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ G),
    IsTorus S.toGrp → IsClosedSubgroup s →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
      (torusCentralizer s).IsRepresentedBy c → IsClosedSubgroup c →
    ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ G), IsUnipotentRadical u →
    ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (v : V ⟶ C), IsUnipotentRadical v →
      SubgroupFunctor.range (v ≫ c) = SubgroupFunctor.range u ⊓ SubgroupFunctor.range c

end Langlands.GroupScheme
