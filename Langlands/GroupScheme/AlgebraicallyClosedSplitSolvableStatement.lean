import Langlands.GroupScheme.SplitSolvable

/-! # Solvable groups are split over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected affine group over an algebraically closed field with
solvable geometric points has an actual represented Ga/Gm normal series. -/
def AlgebraicallyClosedSplitSolvableStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom],
    ConnectedSpace H.X.left → IsSolvableGroupScheme H →
      IsSplitSolvableGroupScheme H

end Langlands.GroupScheme
