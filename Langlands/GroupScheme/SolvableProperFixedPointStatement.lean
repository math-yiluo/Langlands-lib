import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.SchemeAction
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Solvable fixed points on proper schemes over algebraically closed fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected affine solvable group over an algebraically closed field
has a fixed rational point in every nonempty proper scheme on which it acts. -/
def SolvableProperFixedPointStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom],
    ConnectedSpace H.X.left → IsSolvableGroupScheme H →
      ∀ (X : Over (Spec (CommRingCat.of k))),
        IsProper X.hom → Nonempty X.left →
          ∀ (a : SchemeAction H X),
            ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, a.IsFixed x

end Langlands.GroupScheme
