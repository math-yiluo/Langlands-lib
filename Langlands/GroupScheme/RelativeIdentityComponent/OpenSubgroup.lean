import Langlands.GroupScheme.RelativeIdentityComponent.FieldProductCover
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange

/-! # Relative identity components under open subgroup inclusions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeIdentityComponent

section Field

variable {k : Type u} [Field k]
  {H G : GroupScheme (Spec (CommRingCat.of k))}
  (j : H ⟶ G) [IsOpenImmersion j.hom.hom.left]

omit [IsOpenImmersion j.hom.hom.left] in
private theorem map_identityPoint :
    j.hom.hom.left (IdentityComponent.identityPoint H) =
      IdentityComponent.identityPoint G := by
  change (η[H.X] ≫ j.hom.hom).left (IdentityComponent.basePoint k) = _
  rw [IsMonHom.one_hom]
  rfl

/-- An open subgroup contains every point of the smooth ambient group's
identity component. -/
theorem identitySet_subset_range_of_open [Smooth G.X.hom] :
    IdentityComponent.identitySet G ⊆ Set.range j.hom.hom.left := by
  have he : IdentityComponent.identityPoint G ∈ Set.range j.hom.hom.left :=
    ⟨IdentityComponent.identityPoint H, map_identityPoint j⟩
  intro y hy
  obtain ⟨z, hz⟩ := identitySet_subset_range_fieldOpenProduct G j.hom.hom he hy
  refine ⟨μ[H.X].left z, ?_⟩
  have hmul : fieldOpenProduct G j.hom.hom = μ[H.X] ≫ j.hom.hom := by
    exact (IsMonHom.mul_hom j.hom.hom).symm
  rw [hmul] at hz
  exact hz

/-- An open subgroup of a smooth field group has the same identity
component, via its actual inclusion. -/
theorem image_identitySet_of_open [Smooth G.X.hom] :
    j.hom.hom.left '' IdentityComponent.identitySet H =
      IdentityComponent.identitySet G := by
  have hj := map_identityPoint j
  apply Set.Subset.antisymm
  · simpa only [hj] using
      j.hom.hom.left.continuous.image_connectedComponent_subset
        (IdentityComponent.identityPoint H)
  · have hc : _root_.IsPreconnected
        (j.hom.hom.left ⁻¹' IdentityComponent.identitySet G) :=
      isPreconnected_connectedComponent.preimage_of_isOpenMap
        j.hom.hom.left.isEmbedding.injective
        j.hom.hom.left.isOpenEmbedding.isOpenMap
        (identitySet_subset_range_of_open j)
    have hsub : j.hom.hom.left ⁻¹' IdentityComponent.identitySet G ⊆
        IdentityComponent.identitySet H :=
      hc.subset_connectedComponent (x := IdentityComponent.identityPoint H) (by
        change j.hom.hom.left (IdentityComponent.identityPoint H) ∈
          IdentityComponent.identitySet G
        rw [hj]
        exact mem_connectedComponent)
    intro y hy
    obtain ⟨x, rfl⟩ := identitySet_subset_range_of_open j hy
    exact ⟨x, hsub hy, rfl⟩

end Field

/-- Composing a relative identity-component representative with an open
subgroup inclusion into a smooth group preserves the all-test predicate. -/
theorem comp_open {S : Scheme.{u}} {H G C : GroupScheme S}
    (j : H ⟶ G) [IsOpenImmersion j.hom.hom.left] [Smooth G.X.hom]
    (i : C ⟶ H) (hi : IsRelativeIdentityComponent H i) :
    IsRelativeIdentityComponent G (i ≫ j) := by
  let : IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  have : IsOpenImmersion (i ≫ j).hom.hom.left :=
    inferInstanceAs (IsOpenImmersion (i.hom.hom.left ≫ j.hom.hom.left))
  apply IsRelativeIdentityComponent.of_range_residueFiber
  intro s
  let b := S.fromSpecResidueField s
  let Hs := (GroupScheme.baseChange b).obj H
  let Gs := (GroupScheme.baseChange b).obj G
  let js := (GroupScheme.baseChange b).map j
  have : Smooth Gs.X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : IsOpenImmersion js.hom.hom.left :=
    MorphismProperty.of_isPullback
      (overPullback_isPullback b j.hom.hom).flip inferInstance
  rw [Functor.map_comp]
  change Set.range (js.hom.hom.left ∘
    ((GroupScheme.baseChange b).map i).hom.hom.left) =
      IdentityComponent.identitySet Gs
  rw [Set.range_comp, hi.range_residueFiber]
  exact image_identitySet_of_open js

end Langlands.GroupScheme.RelativeIdentityComponent
