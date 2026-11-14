import Langlands.GroupScheme.IntegralModel.SplitRoot

/-! # Reduction of every integral generic-root section -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel.SplitRoot

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (M : IntegralModel R K G) [Smooth M.group.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of R))}
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ M.group)
    (a : characterLattice S) (ha : a ≠ 0)

/-- An ambient integral section with generic point in the intrinsic root
functor factors through the actual closed integral root model. -/
theorem exists_integral_section_of_generic_mem (x : M.integralSections)
    (hx : M.integralPointMap x ∈
      (RelativeRoot.subgroup (M.genericHom i)
        (characterLattice.baseChange (Spec.algebraMap R K) S a)).carrier _) :
    ∃ z : rationalPoints (integralGroup M hS i a ha),
      rationalPoints.map (integralHom M hS i a ha) z = x := by
  rw [← (isRepresentedBy_genericHom M hS i a ha).2] at hx
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
  obtain ⟨z, hz, -⟩ := M.exists_eq_of_integralPointMap_eq
    (integralHom M hS i a ha) (inclusion_isClosedSubgroup M hS i a ha)
    x y hy.symm
  exact ⟨z, hz⟩

variable [IsLocalRing R]

include hS ha in
/-- Reduction of any integral generic-root section belongs to the intrinsic
root functor of the actual base-changed torus and character. -/
theorem reduction_mem_of_generic_mem (x : M.integralSections)
    (hx : M.integralPointMap x ∈
      (RelativeRoot.subgroup (M.genericHom i)
        (characterLattice.baseChange (Spec.algebraMap R K) S a)).carrier _) :
    M.reduction x ∈
      (RelativeRoot.subgroup
        ((GroupScheme.baseChange (residueBaseMap R)).map i)
        (characterLattice.baseChange (residueBaseMap R) S a)).carrier _ := by
  obtain ⟨z, rfl⟩ := exists_integral_section_of_generic_mem M hS i a ha x hx
  have hrep := (integral_properties M hS i a ha).1.baseChange (residueBaseMap R)
  rw [← RelativeRoot.subgroup_baseChange] at hrep
  change baseChangeSectionHom (residueBaseMap R) M.group
    (z ≫ (integralHom M hS i a ha).hom.hom) ∈ _
  rw [baseChangeSectionHom_naturality, ← hrep.2]
  exact ⟨baseChangeSectionHom (residueBaseMap R)
    (integralGroup M hS i a ha) z, rfl⟩

/-- The subgroup of actual integral sections whose generic point is in
the prescribed intrinsic root functor. -/
def integralRootSections : Subgroup M.integralSections :=
  ((RelativeRoot.subgroup (M.genericHom i)
    (characterLattice.baseChange (Spec.algebraMap R K) S a)).carrier _).comap
      M.integralPointMap

/-- Actual reduction restricts to a homomorphism from all integral
generic-root sections into the specialized intrinsic root group. -/
def rootReduction :
    integralRootSections M i a →*
      (RelativeRoot.subgroup
        ((GroupScheme.baseChange (residueBaseMap R)).map i)
        (characterLattice.baseChange (residueBaseMap R) S a)).carrier
          (Over.mk (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))) where
  toFun x := ⟨M.reduction x, reduction_mem_of_generic_mem M hS i a ha x x.property⟩
  map_one' := Subtype.ext (map_one M.reduction)
  map_mul' x y := Subtype.ext (map_mul M.reduction (x : M.integralSections) y)

@[simp] theorem rootReduction_coe (x : integralRootSections M i a) :
    (rootReduction M hS i a ha x : rationalPoints M.specialFibre) = M.reduction x :=
  rfl

end Langlands.GroupScheme.IntegralModel.SplitRoot
