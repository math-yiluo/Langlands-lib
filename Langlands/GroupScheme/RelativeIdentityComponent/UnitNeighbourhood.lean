import Langlands.GroupScheme.RelativeIdentityComponent.SectionComparison
import Langlands.GroupScheme.DominantHomFlat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # An open unit neighbourhood inside the relative identity set -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeIdentityComponent

open Langlands.AlgebraicGeometry

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- The union of the component images from all affine unit neighbourhoods. -/
def unitNeighbourhoodSet : Set G.X.left :=
  ⋃ s : S, (unitNeighbourhood G s).totalι ''
    SectionComponent.componentSet (unitNeighbourhood G s).hom
      (unitNeighbourhood G s).sectionMap (unitNeighbourhood G s).section_hom

/-- Every affine component image belongs to the ambient relative identity set. -/
theorem unitNeighbourhoodSet_subset :
    unitNeighbourhoodSet G ⊆ underlyingSet G := by
  intro x hx
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
  exact image_neighbourhood_componentSet_subset G s hs

/-- The global neighbourhood contains every point of the actual unit section. -/
theorem unitSection_mem_unitNeighbourhoodSet (s : S) :
    unitSection G s ∈ unitNeighbourhoodSet G := by
  obtain ⟨t, ht⟩ := (unitNeighbourhood G s).mem_base
  apply Set.mem_iUnion.mpr
  refine ⟨s, (unitNeighbourhood G s).sectionMap t,
    SectionComponent.section_mem_componentSet _ _ _ t, ?_⟩
  change ((unitNeighbourhood G s).sectionMap ≫ (unitNeighbourhood G s).totalι) t = _
  rw [(unitNeighbourhood G s).section_comp, Scheme.Hom.comp_apply, ht]

/-- Under the generic openness premise, this union is open in the ambient group. -/
theorem isOpen_unitNeighbourhoodSet
    (hEGA : SectionComponent.FlatFinitePresentationOpennessStatement.{u})
    [Smooth G.X.hom] : IsOpen (unitNeighbourhoodSet G) := by
  apply isOpen_iUnion
  intro s
  exact (unitNeighbourhood G s).totalι.isOpenEmbedding.isOpenMap _
    (isOpen_neighbourhood_componentSet G hEGA s)

/-- Multiplication of a smooth group scheme is smooth over any base. -/
theorem smooth_multiplication [Smooth G.X.hom] : Smooth μ[G.X].left := by
  rw [MonObj.mul_eq_mul]
  let : IsIso (DominantHomFlat.shearLeft (𝟙 G.X)).hom.left :=
    (Over.forget S).map_isIso (DominantHomFlat.shearLeft (𝟙 G.X)).hom
  have h := DominantHomFlat.shearLeft_hom_snd (𝟙 G.X)
  simp only [Category.comp_id] at h
  rw [← h, Over.comp_left, Over.snd_left]
  infer_instance

/-- Multiplication of a smooth group scheme is an open map. -/
theorem isOpenMap_multiplication [Smooth G.X.hom] : IsOpenMap μ[G.X].left := by
  let : Smooth μ[G.X].left := smooth_multiplication G
  exact μ[G.X].left.isOpenMap

variable (hEGA : SectionComponent.FlatFinitePresentationOpennessStatement.{u})
  [Smooth G.X.hom]

/-- The open unit neighbourhood as an actual open subset. -/
def unitOpen : G.X.left.Opens :=
  ⟨unitNeighbourhoodSet G, isOpen_unitNeighbourhoodSet G hEGA⟩

/-- The open unit neighbourhood with its actual structure morphism to the base. -/
abbrev unitOver : Over S := Over.mk ((unitOpen G hEGA).ι ≫ G.X.hom)

/-- The inclusion of the open unit neighbourhood over the base. -/
abbrev unitInclusion : unitOver G hEGA ⟶ G.X :=
  Over.homMk (unitOpen G hEGA).ι

instance : IsOpenImmersion (unitInclusion G hEGA).left :=
  inferInstanceAs (IsOpenImmersion (unitOpen G hEGA).ι)

/-- The inclusion has exactly the union of the affine component images as range. -/
theorem range_unitInclusion :
    Set.range (unitInclusion G hEGA).left = unitNeighbourhoodSet G :=
  Scheme.Opens.range_ι _

/-- The neighbourhood inclusion has image in the relative identity set. -/
theorem range_unitInclusion_subset :
    Set.range (unitInclusion G hEGA).left ⊆ underlyingSet G := by
  rw [range_unitInclusion]
  exact unitNeighbourhoodSet_subset G

/-- Multiplication on the actual fibre product of two copies of the neighbourhood. -/
abbrev unitProduct : unitOver G hEGA ⊗ unitOver G hEGA ⟶ G.X :=
  (unitInclusion G hEGA ⊗ₘ unitInclusion G hEGA) ≫ μ[G.X]

instance : IsOpenImmersion (unitInclusion G hEGA ⊗ₘ unitInclusion G hEGA).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
    (Over.w _).symm (Over.w _).symm

/-- The product map on the open unit neighbourhood is smooth. -/
theorem smooth_unitProduct : Smooth (unitProduct G hEGA).left := by
  let : Smooth μ[G.X].left := smooth_multiplication G
  change Smooth ((unitInclusion G hEGA ⊗ₘ unitInclusion G hEGA).left ≫ μ[G.X].left)
  infer_instance

/-- The product image is an open subset of the ambient group scheme. -/
theorem isOpen_range_unitProduct : IsOpen (Set.range (unitProduct G hEGA).left) := by
  let : Smooth (unitProduct G hEGA).left := smooth_unitProduct G hEGA
  exact (unitProduct G hEGA).left.isOpenMap.isOpen_range

end Langlands.GroupScheme.RelativeIdentityComponent
