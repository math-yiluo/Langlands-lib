import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.ProductDetection
import Langlands.GroupScheme.SubgroupIntersection
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The radical and derived subgroup of a connected reductive group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The geometric solvable radical and derived subgroup of a connected
reductive field group have surjective multiplication and finite
scheme-theoretic intersection. -/
def ReductiveRadicalDerivedProductStatement : Prop :=
  ∀ (k : Type u) [Field k] (G R D : GroupScheme (Spec (CommRingCat.of k)))
    (r : R ⟶ G) (d : D ⟶ G),
    IsConnectedReductive G → IsGeometricSolvableRadical r → IsDerivedSubgroup d →
      Surjective (subgroupProductMap r d).left ∧
        IsFinite (subgroupIntersection d r).X.hom

end Langlands.GroupScheme
