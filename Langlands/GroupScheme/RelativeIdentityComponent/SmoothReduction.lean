import Langlands.GroupScheme.RelativeIdentityComponent.ProductImage
import Langlands.GroupScheme.RelativeIdentityComponent.FieldProductCover

/-! # Reduction of smooth relative identity components to finite-presentation openness -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeIdentityComponent

open Langlands.AlgebraicGeometry

variable {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom]
  {P : Over S} (i : P ⟶ G.X)

/-- An open neighbourhood of the whole unit section has product image containing
all residue-fibre identity components. -/
theorem underlyingSet_subset_range_product [IsOpenImmersion i.left]
    (he : ∀ s : S, unitSection G s ∈ Set.range i.left) :
    underlyingSet G ⊆ Set.range (((i ⊗ₘ i) ≫ μ[G.X]).left) := by
  rintro x ⟨s, y, hy, hx⟩
  let j := (Over.pullback (S.fromSpecResidueField s)).map i
  have : IsOpenImmersion j.left :=
    MorphismProperty.of_isPullback
      (overPullback_isPullback (S.fromSpecResidueField s) i).flip
      (inferInstance : IsOpenImmersion i.left)
  have : Smooth (residueFiber G s).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom (S.fromSpecResidueField s)))
  have hj : IdentityComponent.identityPoint (residueFiber G s) ∈ Set.range j.left := by
    rw [range_of_isPullback (overPullback_isPullback (S.fromSpecResidueField s) i)]
    change G.X.hom.fiberι s (IdentityComponent.identityPoint (residueFiber G s)) ∈
      Set.range i.left
    rw [← fiberPoint_unit G s, SectionComponent.fiberι_fiberPoint]
    exact he s
  have hmem := identitySet_subset_range_fieldOpenProduct (residueFiber G s) j hj hy
  change y ∈ Set.range (baseChangedProduct G (S.fromSpecResidueField s) i).left at hmem
  rw [range_baseChangedProduct] at hmem
  change G.X.hom.fiberι s y ∈ Set.range (((i ⊗ₘ i) ≫ μ[G.X]).left) at hmem
  exact hx ▸ hmem

/-- An open unit neighbourhood contained in the relative identity set generates
exactly that set by two-factor multiplication. -/
theorem range_product_eq_underlyingSet [IsOpenImmersion i.left]
    (hi : Set.range i.left ⊆ underlyingSet G)
    (he : ∀ s : S, unitSection G s ∈ Set.range i.left) :
    Set.range (((i ⊗ₘ i) ≫ μ[G.X]).left) = underlyingSet G :=
  Set.Subset.antisymm (product_range_subset_underlyingSet G i hi)
    (underlyingSet_subset_range_product G i he)

variable (hEGA : SectionComponent.FlatFinitePresentationOpennessStatement.{u})

/-- The product image of the constructed global unit neighbourhood. -/
def unitProductImage : Set G.X.left := Set.range (unitProduct G hEGA).left

/-- The constructed global unit neighbourhood generates the entire relative identity set. -/
theorem unitProductImage_eq_underlyingSet :
    unitProductImage G hEGA = underlyingSet G := by
  apply range_product_eq_underlyingSet G (unitInclusion G hEGA)
    (range_unitInclusion_subset G hEGA)
  intro s
  rw [range_unitInclusion]
  exact unitSection_mem_unitNeighbourhoodSet G s

include hEGA

/-- Generic flat finite-presentation openness implies relative openness for every smooth group. -/
theorem isOpen_underlyingSet_of_openness : IsOpen (underlyingSet G) := by
  rw [← unitProductImage_eq_underlyingSet G hEGA]
  exact isOpen_range_unitProduct G hEGA

/-- Generic flat finite-presentation openness implies the exact smooth existence target. -/
theorem smoothExistence_of_openness : SmoothExistenceStatement.{u} := by
  apply smoothExistence_of_isOpen
  intro S G hG
  let := hG
  exact isOpen_underlyingSet_of_openness G hEGA

/-- Generic flat finite-presentation openness implies all three exact smooth structure assertions. -/
theorem smoothStructure_of_openness : SmoothStructureStatement.{u} :=
  smoothStructure_of_existence (smoothExistence_of_openness hEGA)

end Langlands.GroupScheme.RelativeIdentityComponent
