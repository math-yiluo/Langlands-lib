import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.AutomorphicAction

/-! # Equivariant retractions onto normal adjoint subgroups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The projection onto a normal adjoint direct factor is equivariant for a
compatible split-torus action. This is a structural proposition target. -/
def NormalAdjointEquivariantRetractionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G H : GroupScheme (Spec (CommRingCat.of k))),
    IsAdjoint G → IsAdjoint H →
    ∀ (j : H ⟶ G), IsClosedSubgroup j → (SubgroupFunctor.range j).IsNormal →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus S.toGrp →
    ∀ (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H),
      (∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (h : T ⟶ H.X),
        c.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom)) →
      ∃ r : G ⟶ H, j ≫ r = 𝟙 H ∧
        ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X) (g : T ⟶ G.X),
          b.act s g ≫ r.hom.hom = c.act s (g ≫ r.hom.hom)

end Langlands.GroupScheme
