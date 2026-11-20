import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.Torus.Lattice

/-! # Statement: fixed subgroups of torus actions on connected group varieties -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Theorem 13.9 (for tori), Remark 17.40(a) and Corollaries 17.58 and 17.59. Let `G`
be a smooth connected affine group over a field `k`, let a torus `S` act on `G` by group
automorphisms (`a : AutomorphicAction S G`), and let `c : C ⟶ G` be a closed subgroup
representing the all-test fixed subgroup functor `G^S`. Then
1. `C` is smooth and connected;
2. if `G` is connected reductive, then so is `C`;
3. if `k` is algebraically closed, `u : U ⟶ G` is the unipotent radical of `G` and
   `v : V ⟶ C` is the unipotent radical of `C`, then `R_u(G^S) = R_u(G)^S`, that is,
   `R_u(G^S) = R_u(G) ∩ G^S` as all-test subgroup functors of `G`. -/
def TorusActionFixedSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : GroupScheme (Spec (CommRingCat.of k))), IsTorus S →
    ∀ (a : AutomorphicAction S G) (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
      a.fixedSubgroup.IsRepresentedBy c → IsClosedSubgroup c →
      (Smooth C.X.hom ∧ ConnectedSpace C.X.left) ∧
      (IsConnectedReductive G → IsConnectedReductive C) ∧
      (IsAlgClosed k →
        ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (u : U ⟶ G), IsUnipotentRadical u →
        ∀ (V : GroupScheme (Spec (CommRingCat.of k))) (v : V ⟶ C), IsUnipotentRadical v →
          SubgroupFunctor.range (v ≫ c) = SubgroupFunctor.range u ⊓ a.fixedSubgroup)

end Langlands.GroupScheme
