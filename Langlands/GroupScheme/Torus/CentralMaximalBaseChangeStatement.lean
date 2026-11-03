import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Rational.Characters

/-! # Statement: a central maximal torus stays maximal after field extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The forward implication of Milne, Theorem 17.82, for a central torus. If a central closed
torus `j : Z ⟶ H` of a smooth affine group scheme `H` over `k` is maximal, then its pullback
`Z_K ⟶ H_K` is maximal for every field extension `K` of `k`. -/
def CentralMaximalTorusBaseChangeStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (Z : CommGroupScheme (Spec (CommRingCat.of k))) (j : Z.toGrp ⟶ H),
    IsCentral j → IsMaximalTorus j →
      IsMaximalTorus
        (T := (CommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj Z)
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j)

end Langlands.GroupScheme
