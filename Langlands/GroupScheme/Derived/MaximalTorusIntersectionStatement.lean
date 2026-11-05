import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.SubgroupIntersection

/-! # A maximal torus intersects the actual derived subgroup in a torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over any field, the full scheme-theoretic intersection of a maximal torus
with the actual derived subgroup of a connected reductive group is a torus.
This is the torus consequence of KP §2.6(a), printed p. 93. -/
def DerivedMaximalTorusIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (d : D ⟶ G) (t : T.toGrp ⟶ G),
    IsConnectedReductive G → IsDerivedSubgroup d → IsMaximalTorus t →
      IsTorus (subgroupIntersection t d)

end Langlands.GroupScheme
