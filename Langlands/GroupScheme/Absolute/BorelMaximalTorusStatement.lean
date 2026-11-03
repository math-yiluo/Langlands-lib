import Langlands.GroupScheme.Absolute.Borel

/-! # Statement: every Borel subgroup belongs to a Borel pair -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every Borel subgroup of a smooth connected affine group over an algebraically
closed field contains a maximal torus of the ambient group (Milne, after 17.12). -/
def BorelMaximalTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
    IsBorelSubgroup i →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
        IsBorelPair i j

end Langlands.GroupScheme
