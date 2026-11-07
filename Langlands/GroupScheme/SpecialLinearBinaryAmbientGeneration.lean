import Langlands.GroupScheme.SpecialLinearBinaryRootContainment
import Langlands.GroupScheme.Rational.DynamicElementarySubgroup

/-! # Full split binary images in the actual parabolic elementary subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.BinaryRoot

variable {k : Type u} [Field k]
  {A G : GroupScheme (Spec (CommRingCat.of k))}

/-- Every actual upper-root point of a split binary source maps to an actual
geometric parabolic-radical generator in a connected reductive target. -/
theorem map_upperPoint_mem_parabolicUnipotentPointSet
    (hG : IsConnectedReductive G)
    (f : SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⟶ G)
    (x : rationalPoints (VectorGroup.groupScheme (CommRingCat.of k) 1)) :
    rationalPoints.map f (rationalPoints.map (upperMap (CommRingCat.of k)) x) ∈
      parabolicUnipotentPointSet G := by
  have hx : rationalPoints.map (upperMap (CommRingCat.of k)) x ∈
      (Dynamic.unipotent (upperCocharacter (CommRingCat.of k))).carrier
        (Over.mk (𝟙 _)) :=
    upperRoot_range_le_dynamicUnipotent (CommRingCat.of k) _
      (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
  exact mem_parabolicUnipotentPointSet_of_dynamicUnipotent hG
    (upperCocharacter (CommRingCat.of k) ≫ f)
    (Dynamic.unipotent_le_comap (upperCocharacter (CommRingCat.of k)) f _ hx)

/-- The full rational image of any actual split SL₂ homomorphism lies in the
target's actual parabolic elementary subgroup, over every field. -/
theorem rationalPoints_range_le_parabolicElementarySubgroup
    (hG : IsConnectedReductive G)
    (f : SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k) ⟶ G) :
    (rationalPoints.map f).range ≤ parabolicElementarySubgroup G :=
  rationalPoints_range_le_of_upper_dynamic f (parabolicElementarySubgroup G)
    (dynamicUnipotent_le_parabolicElementarySubgroup hG
      (upperCocharacter (CommRingCat.of k) ≫ f))

/-- An actual ground-field model isomorphic to split SL₂ has the same
full-image containment under any actual map into a connected reductive group. -/
theorem rationalPoints_range_le_parabolicElementarySubgroup_of_iso
    (hG : IsConnectedReductive G)
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) (a : A ⟶ G) :
    (rationalPoints.map a).range ≤ parabolicElementarySubgroup G :=
  rationalPoints_range_le_of_iso_upper_dynamic e a (parabolicElementarySubgroup G)
    (dynamicUnipotent_le_parabolicElementarySubgroup hG
      (upperCocharacter (CommRingCat.of k) ≫ e.inv ≫ a))

/-- The original full point homomorphism of an actual split binary model,
with codomain restricted to the ambient parabolic elementary subgroup. -/
def rationalPointsToParabolicElementarySubgroup
    (hG : IsConnectedReductive G)
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) (a : A ⟶ G) :
    rationalPoints A →* parabolicElementarySubgroup G :=
  (rationalPoints.map a).codRestrict (parabolicElementarySubgroup G) fun x =>
    rationalPoints_range_le_parabolicElementarySubgroup_of_iso hG e a ⟨x, rfl⟩

@[simp]
theorem rationalPointsToParabolicElementarySubgroup_apply_coe
    (hG : IsConnectedReductive G)
    (e : A ≅ SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) (a : A ⟶ G)
    (x : rationalPoints A) :
    (rationalPointsToParabolicElementarySubgroup hG e a x : rationalPoints G) =
      rationalPoints.map a x := rfl

end Langlands.GroupScheme.SpecialLinear.BinaryRoot
