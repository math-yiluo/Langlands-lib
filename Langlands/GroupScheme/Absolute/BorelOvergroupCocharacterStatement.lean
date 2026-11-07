import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Dynamic.Basic

/-! # Statement: actual cocharacters for absolute smooth Borel overgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The absolute, point-level cocharacter presentation of a smooth closed
overgroup of a specified Borel pair. Derived from Milne 21.91--21.92, retaining
the reductive scope and actual integral cocharacters of the specified torus. -/
def AbsoluteBorelOvergroupCocharacterStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (_hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
    IsSplitTorus T.toGrp →
      ∀ (P : GroupScheme (Spec (CommRingCat.of k))) [Smooth P.X.hom] (i : P ⟶ G),
        IsClosedSubgroup i →
          ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ P),
            IsBorelPair (b ≫ i) j →
              ∃ ζ : cocharacterLattice T,
                (SubgroupFunctor.range i).carrier
                    (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
                  (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ j)).carrier
                    (Over.mk (𝟙 (Spec (CommRingCat.of k))))

end Langlands.GroupScheme
