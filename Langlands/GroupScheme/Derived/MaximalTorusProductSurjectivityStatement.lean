import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Rational.ProductDetection

/-! # Surjectivity of derived-subgroup and maximal-torus multiplication -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A connected reductive field group is the scheme-theoretic product of its
actual derived subgroup and any specified maximal torus. -/
def DerivedMaximalTorusProductSurjectivityStatement : Prop :=
  ∀ (k : Type u) [Field k] (H D : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (d : D ⟶ H) (i : T.toGrp ⟶ H),
    IsConnectedReductive H → IsDerivedSubgroup d → IsMaximalTorus i →
      Surjective (subgroupProductMap d i).left

end Langlands.GroupScheme
