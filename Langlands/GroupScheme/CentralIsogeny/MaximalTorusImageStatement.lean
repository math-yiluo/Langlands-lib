import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Statement: central isogenies carry maximal tori onto maximal tori -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Images of maximal tori under central isogenies** (derived from Milne Proposition 17.20
and Theorem 17.82). Let `π : G ⟶ H` be a central isogeny of connected reductive groups over a
field and `i : T ⟶ G` a maximal torus. A closed torus `j : S ⟶ H` with
`i ≫ π = groupHom f ≫ j` for a homomorphism `f : T ⟶ S` whose underlying morphism of schemes
is surjective is a maximal torus of `H`: maximal among all closed tori, not only among split
ones. -/
def CentralIsogenyMaximalTorusImageStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → IsConnectedReductive H →
    ∀ (π : G ⟶ H), IsCentralIsogeny π →
    ∀ (T S : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ G) (j : S.toGrp ⟶ H) (f : T ⟶ S),
      IsMaximalTorus i → IsTorus S.toGrp → IsClosedSubgroup j →
      Surjective (CommGroupScheme.groupHom f).hom.hom.left →
      i ≫ π = CommGroupScheme.groupHom f ≫ j →
      IsMaximalTorus j

end Langlands.GroupScheme
