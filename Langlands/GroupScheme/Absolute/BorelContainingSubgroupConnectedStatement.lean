import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: a smooth closed subgroup containing a Borel is connected -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A smooth closed subgroup containing a Borel subgroup of a smooth connected
affine group over an algebraically closed field is connected (Milne, 17.49). -/
def BorelContainingSubgroupConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (P B : GroupScheme (Spec (CommRingCat.of k)))
    (i : P ⟶ G) (j : B ⟶ G) (f : B ⟶ P),
    IsClosedSubgroup i → Smooth P.X.hom → IsBorelSubgroup j → f ≫ i = j →
      ConnectedSpace P.X.left

end Langlands.GroupScheme
