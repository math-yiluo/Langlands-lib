import Langlands.GroupScheme.SpecialLinearWeilRootContainment
import Langlands.GroupScheme.Rational.DynamicElementarySubgroup

/-! # Actual Weil-restricted special-linear images in the parabolic elementary subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.WeilRoot

variable {n : Type} [Fintype n] [DecidableEq n]
  (F E : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {A G : GroupScheme (Spec (CommRingCat.of F))}

/-- Every actual restricted coordinate-root point maps to an actual geometric
parabolic-radical generator of a connected reductive target. -/
theorem map_rootPoint_mem_parabolicUnipotentPointSet
    (hG : IsConnectedReductive G)
    (f : groupScheme (n := n) F E ⟶ G) {i j : n} (hij : i ≠ j)
    (x : rationalPoints (additiveScheme F E)) :
    rationalPoints.map f (rationalPoints.map (rootMap F E hij) x) ∈
      parabolicUnipotentPointSet G := by
  have hx : rationalPoints.map (rootMap F E hij) x ∈
      (Dynamic.unipotent (cocharacter F E hij)).carrier (Over.mk (𝟙 _)) :=
    root_range_le_dynamicUnipotent F E hij _
      (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
  exact mem_parabolicUnipotentPointSet_of_dynamicUnipotent hG
    (cocharacter F E hij ≫ f)
    (Dynamic.unipotent_le_comap (cocharacter F E hij) f _ hx)

/-- The full rational image of an actual Weil-restricted split special-linear
source lies in the target's actual parabolic elementary subgroup. -/
theorem rationalPoints_range_le_parabolicElementarySubgroup
    (hG : IsConnectedReductive G)
    (f : groupScheme (n := n) F E ⟶ G) :
    (rationalPoints.map f).range ≤ parabolicElementarySubgroup G :=
  rationalPoints_range_le_of_coordinate_dynamics F E f (parabolicElementarySubgroup G)
    fun _ _ hij => dynamicUnipotent_le_parabolicElementarySubgroup hG
      (cocharacter F E hij ≫ f)

/-- Any specified actual model of the restricted source has the same full
image containment under its original rational point map. -/
theorem rationalPoints_range_le_parabolicElementarySubgroup_of_iso
    (hG : IsConnectedReductive G)
    (e : A ≅ groupScheme (n := n) F E) (a : A ⟶ G) :
    (rationalPoints.map a).range ≤ parabolicElementarySubgroup G :=
  rationalPoints_range_le_of_iso_coordinate_dynamics F E e a
    (parabolicElementarySubgroup G) fun _ _ hij =>
      dynamicUnipotent_le_parabolicElementarySubgroup hG
        (cocharacter F E hij ≫ e.inv ≫ a)

/-- The original full rational point homomorphism, with its codomain restricted
to the target's actual parabolic elementary subgroup. -/
def rationalPointsToParabolicElementarySubgroup
    (hG : IsConnectedReductive G)
    (e : A ≅ groupScheme (n := n) F E) (a : A ⟶ G) :
    rationalPoints A →* parabolicElementarySubgroup G :=
  (rationalPoints.map a).codRestrict (parabolicElementarySubgroup G) fun x =>
    rationalPoints_range_le_parabolicElementarySubgroup_of_iso F E hG e a ⟨x, rfl⟩

@[simp]
theorem rationalPointsToParabolicElementarySubgroup_apply_coe
    (hG : IsConnectedReductive G)
    (e : A ≅ groupScheme (n := n) F E) (a : A ⟶ G)
    (x : rationalPoints A) :
    (rationalPointsToParabolicElementarySubgroup F E hG e a x :
      rationalPoints G) = rationalPoints.map a x := rfl

end Langlands.GroupScheme.SpecialLinear.WeilRoot
