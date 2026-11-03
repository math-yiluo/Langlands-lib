import Langlands.GroupScheme.Absolute.Borel

/-! # Containing a given smooth connected solvable subgroup in a Borel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every given smooth connected solvable closed subgroup of a smooth affine connected group
over an algebraically closed field factors through an actual Borel subgroup. -/
def SolvableSubgroupBorelContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G)
    [Smooth H.X.hom] [ConnectedSpace H.X.left],
    IsClosedSubgroup j → IsSolvableGroupScheme H →
      ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G) (f : H ⟶ B),
        IsBorelSubgroup i ∧ f ≫ i = j

end Langlands.GroupScheme
