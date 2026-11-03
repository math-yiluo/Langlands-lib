import Langlands.GroupScheme.CentralIsogeny.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Lifting maximal split tori through a central isogeny of connected reductive groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field `k`, let `π : G ⟶ H` be a central isogeny of connected reductive group
schemes and `i : S ⟶ H` a maximal split torus. Then there are a commutative group scheme `T`,
a maximal split torus `j : T ⟶ G` and a homomorphism `f : T ⟶ S` of commutative group schemes
with `j ≫ π = groupHom f ≫ i`, whose underlying scheme morphism is flat, surjective and locally
of finite presentation. The torus `T` is not identified with the full inverse image of `S`. -/
def CentralIsogenyMaximalSplitTorusLiftStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → IsConnectedReductive H →
    ∀ (π : G ⟶ H), IsCentralIsogeny π →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ H),
      IsMaximalSplitTorus i →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
        (f : T ⟶ S),
        IsMaximalSplitTorus j ∧
        j ≫ π = CommGroupScheme.groupHom f ≫ i ∧
        Flat (CommGroupScheme.groupHom f).hom.hom.left ∧
        Surjective (CommGroupScheme.groupHom f).hom.hom.left ∧
        LocallyOfFinitePresentation (CommGroupScheme.groupHom f).hom.hom.left

end Langlands.GroupScheme
