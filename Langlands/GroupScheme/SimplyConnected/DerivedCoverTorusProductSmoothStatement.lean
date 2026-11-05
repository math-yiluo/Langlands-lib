import Langlands.GroupScheme.SimplyConnected.DerivedCover
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Rational.ProductDetection

/-! # Smoothness of the derived-cover and maximal-torus multiplication map -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Multiplication from a simply connected cover of the actual derived subgroup and a
maximal torus of a connected reductive field group is smooth, in every characteristic. -/
def DerivedCoverTorusProductSmoothStatement : Prop :=
  ∀ (k : Type u) [Field k] (H D C : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (d : D ⟶ H) (π : C ⟶ D) (i : T.toGrp ⟶ H),
    IsSimplyConnectedDerivedCover d π → IsMaximalTorus i →
      Smooth (subgroupProductMap (π ≫ d) i).left

end Langlands.GroupScheme
