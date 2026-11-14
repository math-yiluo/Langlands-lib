import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Torus.Lattice

/-! # Statement: Borel subgroups of the centralizer of a torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Theorem 17.46. Let `G` be a smooth connected affine group over a field `k`, let
`s : S ⟶ G` be a closed torus and let `c : C ⟶ G` be a closed subgroup representing the
centralizer `C_G(S)`.
* For every geometric Borel subgroup `b : B ⟶ G` containing `S`, the intersection
  `C_G(S) ∩ B` is the range of a geometric Borel subgroup of `C`.
* If `k` is algebraically closed, every Borel subgroup of `C` arises in this way from a Borel
  subgroup of `G` containing `S`. -/
def TorusCentralizerBorelStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ G),
    IsTorus S.toGrp → IsClosedSubgroup s →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
      (torusCentralizer s).IsRepresentedBy c → IsClosedSubgroup c →
      (∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsGeometricBorelSubgroup b → SubgroupFunctor.range s ≤ SubgroupFunctor.range b →
          ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ C),
            IsGeometricBorelSubgroup d ∧
              SubgroupFunctor.range (d ≫ c) =
                SubgroupFunctor.range c ⊓ SubgroupFunctor.range b) ∧
      (IsAlgClosed k →
        ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ C), IsBorelSubgroup d →
          ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
            IsBorelSubgroup b ∧ SubgroupFunctor.range s ≤ SubgroupFunctor.range b ∧
              SubgroupFunctor.range (d ≫ c) =
                SubgroupFunctor.range c ⊓ SubgroupFunctor.range b)

end Langlands.GroupScheme
