import Langlands.GroupScheme.SimplyConnected.DerivedCover
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.SubgroupIntersection

/-! # The full maximal-torus preimage in a simply connected derived cover -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual scheme-theoretic inverse image of a maximal torus in a simply
connected cover of the derived group is a torus, over every field. -/
def DerivedCoverMaximalTorusPreimageStatement : Prop :=
  ∀ (k : Type u) [Field k] (H D C : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (d : D ⟶ H) (π : C ⟶ D) (i : T.toGrp ⟶ H),
    IsSimplyConnectedDerivedCover d π → IsMaximalTorus i →
      IsTorus (subgroupIntersection (π ≫ d) i)

end Langlands.GroupScheme
