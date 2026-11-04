import Langlands.GroupScheme.Cartan.Basic
import Langlands.GroupScheme.Nilpotent.Basic
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: structure of Cartan subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The structural assertion of Milne, Proposition 17.44: a Cartan subgroup
of a smooth connected affine group over a field is smooth, connected, and
geometrically nilpotent. Cartans are actual closed representatives of
all-test maximal-torus centralizers. -/
def CartanStructureStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (C : GroupScheme (Spec (CommRingCat.of k))) (i : C ⟶ G),
    IsCartanSubgroup i →
      Smooth C.X.hom ∧ ConnectedSpace C.X.left ∧ IsNilpotentGroupScheme C

end Langlands.GroupScheme
