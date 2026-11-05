import Langlands.GroupScheme.RelativeIdentityComponent
import Mathlib.AlgebraicGeometry.Fiber

/-! # Comparing represented relative identity components with residue fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeIdentityComponent

variable {S : Scheme.{u}} (G : GroupScheme S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The image of a pulled-back test point is the preimage of its original image
under the inclusion of the residue fibre. -/
theorem range_residueFiberPoint {T : Over S} (x : T ⟶ G.X) (s : S) :
    Set.range (residueFiberPoint G x s).left =
      G.X.hom.fiberι s ⁻¹' Set.range x.left := by
  change Set.range
      (pullback.lift (pullback.fst T.hom (S.fromSpecResidueField s) ≫ x.left)
        (pullback.snd T.hom (S.fromSpecResidueField s)) _) =
      (pullback.fst G.X.hom (S.fromSpecResidueField s)) ⁻¹' Set.range x.left
  have hmap :
      pullback.lift (pullback.fst T.hom (S.fromSpecResidueField s) ≫ x.left)
        (pullback.snd T.hom (S.fromSpecResidueField s))
          (by simp [pullback.condition]) =
        pullback.map T.hom (S.fromSpecResidueField s)
          G.X.hom (S.fromSpecResidueField s)
          x.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp
  rw [hmap, Scheme.Pullback.range_map]
  simp

/-- The represented subgroup inclusion satisfies the defining fibre-image
condition. -/
theorem inclusion_inRelativeIdentityComponent {H : GroupScheme S} (i : H ⟶ G)
    (hi : IsRelativeIdentityComponent G i) :
    InRelativeIdentityComponent G i.hom.hom :=
  (hi.factors_iff H.X i.hom.hom).mp ⟨𝟙 _, Category.id_comp _⟩

/-- Every residue-fibre image of a represented subgroup lies in the identity
component of the ambient residue fibre. -/
theorem range_residueFiberInclusion_subset {H : GroupScheme S} (i : H ⟶ G)
    (hi : IsRelativeIdentityComponent G i) (s : S) :
    Set.range ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i).hom.hom.left ⊆
      IdentityComponent.identitySet (residueFiber G s) :=
  inclusion_inRelativeIdentityComponent G i hi s

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The image of any representative meets each residue fibre in precisely the
identity component. -/
theorem preimage_range_inclusion_eq_identitySet {H : GroupScheme S} (i : H ⟶ G)
    (hi : IsRelativeIdentityComponent G i) (s : S) :
    G.X.hom.fiberι s ⁻¹' Set.range i.hom.hom.left =
      IdentityComponent.identitySet (residueFiber G s) := by
  apply Set.Subset.antisymm
  · have h := inclusion_inRelativeIdentityComponent G i hi s
    rwa [range_residueFiberPoint] at h
  · intro y hy
    let x : G.X.left := G.X.hom.fiberι s y
    let T : Over S := Over.mk (G.X.left.fromSpecResidueField x ≫ G.X.hom)
    let a : T ⟶ G.X := Over.homMk (G.X.left.fromSpecResidueField x)
    have ha : InRelativeIdentityComponent G a := by
      intro t z hz
      rw [range_residueFiberPoint] at hz
      change G.X.hom.fiberι t z ∈ Set.range (G.X.left.fromSpecResidueField x) at hz
      rw [Scheme.range_fromSpecResidueField, Set.mem_singleton_iff] at hz
      have hzbase : G.X.hom (G.X.hom.fiberι t z) = t := by
        have hmem : G.X.hom.fiberι t z ∈ Set.range (G.X.hom.fiberι t) := ⟨z, rfl⟩
        rwa [Scheme.Hom.range_fiberι] at hmem
      have hybase : G.X.hom (G.X.hom.fiberι s y) = s := by
        have hmem : G.X.hom.fiberι s y ∈ Set.range (G.X.hom.fiberι s) := ⟨y, rfl⟩
        rwa [Scheme.Hom.range_fiberι] at hmem
      have ht : t = s := hzbase.symm.trans ((congrArg G.X.hom hz).trans hybase)
      subst t
      have hzy : z = y := (G.X.hom.fiberι s).isEmbedding.injective hz
      exact hzy ▸ hy
    obtain ⟨b, hb⟩ := (hi.factors_iff T a).mpr ha
    have hx : x ∈ Set.range a.left := by
      change x ∈ Set.range (G.X.left.fromSpecResidueField x)
      rw [Scheme.range_fromSpecResidueField]
      exact Set.mem_singleton _
    obtain ⟨p, hp⟩ := hx
    refine ⟨b.left p, ?_⟩
    change (b ≫ i.hom.hom).left p = x
    rw [hb]
    exact hp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Base changing any represented relative identity-component inclusion to a
residue field has range exactly the ambient identity component. -/
theorem range_residueFiberInclusion {H : GroupScheme S} (i : H ⟶ G)
    (hi : IsRelativeIdentityComponent G i) (s : S) :
    Set.range ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i).hom.hom.left =
      IdentityComponent.identitySet (residueFiber G s) := by
  change Set.range (residueFiberPoint G i.hom.hom s).left = _
  rw [range_residueFiberPoint, preimage_range_inclusion_eq_identitySet G i hi]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The represented image is closed in the subspace over each point of the
base. This only uses closedness of connected components. -/
theorem isClosed_fiber_preimage_range_inclusion {H : GroupScheme S} (i : H ⟶ G)
    (hi : IsRelativeIdentityComponent G i) (s : S) :
    IsClosed ((Subtype.val : (G.X.hom ⁻¹' {s}) → G.X.left) ⁻¹'
      Set.range i.hom.hom.left) := by
  apply (G.X.hom.fiberHomeo s).isClosed_preimage.mp
  change IsClosed (G.X.hom.fiberι s ⁻¹' Set.range i.hom.hom.left)
  rw [preimage_range_inclusion_eq_identitySet G i hi]
  exact isClosed_connectedComponent

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The intersection of the represented image with a closed fibre is closed
in the total space. -/
theorem isClosed_inter_fiber_range_inclusion {H : GroupScheme S} (i : H ⟶ G)
    (hi : IsRelativeIdentityComponent G i) (s : S) (hs : IsClosed ({s} : Set S)) :
    IsClosed (Set.range i.hom.hom.left ∩ (G.X.hom ⁻¹' {s})) := by
  have hι : Topology.IsClosedEmbedding (G.X.hom.fiberι s) :=
    ⟨(G.X.hom.fiberι s).isEmbedding, by
      rw [Scheme.Hom.range_fiberι]
      exact hs.preimage G.X.hom.continuous⟩
  have hc : IsClosed (G.X.hom.fiberι s ⁻¹' Set.range i.hom.hom.left) := by
    rw [preimage_range_inclusion_eq_identitySet G i hi]
    exact isClosed_connectedComponent
  have h := hι.isClosedMap _ hc
  rwa [Set.image_preimage_eq_inter_range, Scheme.Hom.range_fiberι] at h

end Langlands.GroupScheme.RelativeIdentityComponent
