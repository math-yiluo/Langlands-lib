import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: the quotient by a central maximal torus contains no torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Lemma 16.43, as used in the proof of Theorem 17.82: if a central closed torus
`j : Z ⟶ H` of a smooth affine group scheme over `k` is maximal and `q : H ⟶ Q` is an fppf
quotient map with kernel `Z`, then every homomorphism from a torus over `k` to `Q` is trivial on
all points. -/
def CentralMaximalTorusQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (Z : CommGroupScheme (Spec (CommRingCat.of k))) (j : Z.toGrp ⟶ H),
    IsCentral j → IsMaximalTorus j →
    ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : H ⟶ Q),
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
        ∀ g : T.toGrp ⟶ Q, SubgroupFunctor.range g = ⊥

end Langlands.GroupScheme
