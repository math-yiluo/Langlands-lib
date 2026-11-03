import Langlands.GroupScheme.Torus.Maximal
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Finiteness of the full normalizer image of a split torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a closed split torus in an affine algebraic group, the image of the actual
normalizer-point action on its whole integral character lattice is finite. -/
def SplitTorusWeylImageFiniteStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i),
      haveI : IsClosedImmersion i.hom.hom.left := hi
      Finite (weylImage i)

end Langlands.GroupScheme
