import Langlands.GroupScheme.Torus.Maximal
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Statement: reflection of maximal tori along a finite homomorphism -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `π : G ⟶ H` be a homomorphism of connected reductive groups over a field whose underlying
morphism of schemes is finite. A closed torus `j : T ⟶ G` whose composite with `π` equals
`groupHom f ≫ i`, for a maximal torus `i : S ⟶ H` and a homomorphism `f : T ⟶ S` whose underlying
morphism of schemes is surjective, is a maximal torus of `G`: maximal among all closed tori, not
only among split ones. -/
def FiniteHomMaximalTorusReflectionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → IsConnectedReductive H →
    ∀ (π : G ⟶ H), IsFinite π.hom.hom.left →
    ∀ (T S : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : T.toGrp ⟶ G) (i : S.toGrp ⟶ H) (f : T ⟶ S),
      IsTorus T.toGrp → IsClosedSubgroup j → IsMaximalTorus i →
      Surjective (CommGroupScheme.groupHom f).hom.hom.left →
      j ≫ π = CommGroupScheme.groupHom f ≫ i →
      IsMaximalTorus j

end Langlands.GroupScheme
