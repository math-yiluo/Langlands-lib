import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.AutomorphicAction

/-! # A fixed split torus containing the full centre -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, a split-torus action on a connected
reductive group fixes a closed split torus containing the whole scheme-theoretic
centre. This is a structural proposition target. -/
def FixedCenterContainingTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))), IsSplitTorus S.toGrp →
    ∀ b : AutomorphicAction S.toGrp G,
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
        IsSplitTorus T.toGrp ∧ IsClosedSubgroup j ∧
        center G ≤ SubgroupFunctor.range j ∧
        ∀ (U : Over (Spec (CommRingCat.of k))) (s : U ⟶ S.X) (t : U ⟶ T.X),
          b.act s (t ≫ j.hom.hom) = t ≫ j.hom.hom

end Langlands.GroupScheme
