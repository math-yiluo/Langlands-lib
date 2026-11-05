import Langlands.AlgebraicGeometry.SectionComponentFunctoriality
import Langlands.AlgebraicGeometry.AffineSectionNeighbourhood
import Langlands.AlgebraicGeometry.SectionComponentOpennessStatement
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Langlands.GroupScheme.RelativeIdentityComponent.UnderlyingSet
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Section components at the unit of a group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeIdentityComponent

open Langlands.AlgebraicGeometry

variable {S : Scheme.{u}} (G : GroupScheme S)

/-- The actual unit section on the underlying schemes. -/
abbrev unitSection : S ⟶ G.X.left := η[G.X].left

@[reassoc (attr := simp)]
theorem unitSection_comp : unitSection G ≫ G.X.hom = 𝟙 S :=
  (η[G.X]).w

@[reassoc (attr := simp)]
theorem residueFiber_unit_fiberι (s : S) :
    η[(residueFiber G s).X].left ≫ G.X.hom.fiberι s =
      S.fromSpecResidueField s ≫ unitSection G := by
  change (Functor.LaxMonoidal.ε (Over.pullback (S.fromSpecResidueField s))).left ≫
    ((Over.pullback (S.fromSpecResidueField s)).map η[G.X]).left ≫
      pullback.fst _ _ = _
  have hf :
      ((Over.pullback (S.fromSpecResidueField s)).map η[G.X]).left ≫
        pullback.fst _ _ =
      pullback.fst (𝟙 S) (S.fromSpecResidueField s) ≫ unitSection G :=
    pullback.lift_fst _ _ _
  rw [hf]
  change (Functor.LaxMonoidal.ε (Over.pullback (S.fromSpecResidueField s))).left ≫
    pullback.fst (𝟙 S) (S.fromSpecResidueField s) ≫ unitSection G = _
  rw [Over.ε_pullback_left]
  have h : pullback.fst (𝟙 S) (S.fromSpecResidueField s) =
      pullback.snd (𝟙 S) (S.fromSpecResidueField s) ≫ S.fromSpecResidueField s := by
    simpa using pullback.condition (f := 𝟙 S) (g := S.fromSpecResidueField s)
  rw [h]
  simp

/-- The section-selected fibre point is the actual identity point of the fibre group. -/
theorem fiberPoint_unit (s : S) :
    SectionComponent.fiberPoint G.X.hom (unitSection G) (unitSection_comp G) s =
      IdentityComponent.identityPoint (residueFiber G s) := by
  apply (G.X.hom.fiberι s).isEmbedding.injective
  rw [SectionComponent.fiberι_fiberPoint]
  symm
  change (η[(residueFiber G s).X].left ≫ G.X.hom.fiberι s) _ = _
  rw [residueFiber_unit_fiberι]
  exact congrArg (unitSection G) (Scheme.fromSpecResidueField_apply s _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The generic component union at the unit equals the all-test relative identity set. -/
theorem componentSet_unit :
    SectionComponent.componentSet G.X.hom (unitSection G) (unitSection_comp G) =
      underlyingSet G := by
  ext x
  constructor
  · rintro ⟨s, z, hz, hx⟩
    exact ⟨s, z, by simpa only [fiberPoint_unit, IdentityComponent.identitySet] using hz, hx⟩
  · rintro ⟨s, z, hz, hx⟩
    exact ⟨s, z, by simpa only [fiberPoint_unit, IdentityComponent.identitySet] using hz, hx⟩

/-- The chosen affine section neighbourhood, for the unit of a group scheme. -/
abbrev unitNeighbourhood (s : S) :
    AffineSectionNeighbourhood G.X.hom (unitSection G) s :=
  affineSectionNeighbourhood G.X.hom (unitSection G) (unitSection_comp G) s

/-- The component union in a unit neighbourhood lands in the relative identity set. -/
theorem image_neighbourhood_componentSet_subset (s : S) :
    (unitNeighbourhood G s).totalι ''
      SectionComponent.componentSet (unitNeighbourhood G s).hom
        (unitNeighbourhood G s).sectionMap (unitNeighbourhood G s).section_hom ⊆
      underlyingSet G := by
  rw [← componentSet_unit]
  exact SectionComponent.image_componentSet_subset _ _
    (unitNeighbourhood G s).comm (unitNeighbourhood G s).section_comp

/-- The finite-presentation openness theorem applies to each smooth affine unit neighbourhood. -/
theorem isOpen_neighbourhood_componentSet
    (hEGA : SectionComponent.FlatFinitePresentationOpennessStatement.{u})
    [Smooth G.X.hom] (s : S) :
    IsOpen (SectionComponent.componentSet (unitNeighbourhood G s).hom
      (unitNeighbourhood G s).sectionMap (unitNeighbourhood G s).section_hom) := by
  let := SmoothReducedProof.geometricallyReduced_of_smooth (unitNeighbourhood G s).hom
  exact hEGA _ _ _ _ _ inferInstance inferInstance inferInstance inferInstance inferInstance

end Langlands.GroupScheme.RelativeIdentityComponent
