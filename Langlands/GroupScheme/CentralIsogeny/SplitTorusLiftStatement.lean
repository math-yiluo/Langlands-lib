import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Torus.Maximal

/-! # Lifting split maximal tori through a central isogeny of connected reductive groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field `k`, let `π : G ⟶ H` be a central isogeny of connected reductive group
schemes and `i : S ⟶ H` a maximal torus with `S` split. Then there are a commutative group
scheme `T`, a maximal torus `j : T ⟶ G` with `T` split, and a homomorphism `f : T ⟶ S` of
commutative group schemes with `j ≫ π = groupHom f ≫ i`. -/
def CentralIsogenySplitMaximalTorusLiftStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → IsConnectedReductive H →
    ∀ (π : G ⟶ H), IsCentralIsogeny π →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ H),
      IsSplitTorus S.toGrp → IsMaximalTorus i →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G) (f : T ⟶ S),
        IsSplitTorus T.toGrp ∧ IsMaximalTorus j ∧ j ≫ π = CommGroupScheme.groupHom f ≫ i

end Langlands.GroupScheme
