/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Section components in a cartesian square

Source: Stacks Project, Tag 055M. The arbitrary-square proof generalizes the argument in
`WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat`, which cannot be imported
here because its slicing theorem depends on the section-component noetherian model.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

/-- Section-component loci commute with any cartesian square compatible with the sections.

Source: Stacks Project, Tag 055M (more-morphisms.tex, lemma-base-change-connected-along-section).
Proof: in each fibre, the section point is rational. Its connected component is open in
that locally noetherian fibre and is geometrically connected. Its inverse image in the
base-changed fibre is therefore connected and contains the new section point. This proves
one inclusion. The continuous image of the new component is connected and contains the
old section point, proving the other inclusion. Work directly in the given cartesian
square: restrict its first projection to the open representing the old fibre component,
then compare residue-field fibres. The section compatibility identifies the distinguished
points without a canonical-pullback or homeomorphism-transport lemma.

(blueprint: lem-sbc-section-component-cartesian) -/
theorem section_component_preimage_of_isPullback {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    (a : X' ⟶ X) (f' : X' ⟶ Y') (b : Y' ⟶ Y) (h : IsPullback a f' f b)
    (σ' : Y' ⟶ X') (hσ' : σ' ≫ f' = 𝟙 Y') (hcompat : σ' ≫ a = b ≫ σ) :
    a ⁻¹' {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (σ (f x))} =
      {x' : X' | x' ∈ connectedComponentIn (f' ⁻¹' {f' x'}) (σ' (f' x'))} := by
  ext x'
  set y' := f' x'
  set p := σ' y'
  have hfx : f (a x') = b y' := by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  have hp₁ : a p = σ (b y') := by
    rw [← Scheme.Hom.comp_apply, hcompat, Scheme.Hom.comp_apply]
  have hp₂ : f' p = y' := by
    rw [← Scheme.Hom.comp_apply, hσ']
    rfl
  have hσy (y : Y) : f (σ y) = y := by
    rw [← Scheme.Hom.comp_apply, hσ]
    rfl
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hfx]
  constructor
  · intro hx
    have hσmem : σ (b y') ∈ f ⁻¹' {b y'} := hσy _
    obtain ⟨t, ht, hct⟩ := isOpen_induced_iff.mp
      (isOpen_connectedComponent (x := (⟨σ (b y'), hσmem⟩ : f ⁻¹' {b y'})))
    let U : X.Opens := ⟨t, ht⟩
    have hU : (U : Set X) ∩ f ⁻¹' {b y'} =
        connectedComponentIn (f ⁻¹' {b y'}) (σ (b y')) := by
      rw [connectedComponentIn_eq_image hσmem, ← hct, Set.image_preimage_eq_inter_range,
        Subtype.range_coe]
      rfl
    have hσU : σ (b y') ∈ U := (hU.ge (mem_connectedComponentIn (hσy _))).1
    let W := a ⁻¹ᵁ U
    have hW := (isPullback_morphismRestrict a U).paste_vert h
    have hfactor : Set.range (Y.fromSpecResidueField (b y') ≫ σ) ⊆ Set.range U.ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
      exact hσU
    let s := IsOpenImmersion.lift U.ι (Y.fromSpecResidueField (b y') ≫ σ) hfactor
    have hs : s ≫ U.ι = Y.fromSpecResidueField (b y') ≫ σ :=
      IsOpenImmersion.lift_fac _ _ _
    have hq : _root_.IsPreconnected ((U.ι ≫ f) ⁻¹' {b y'}) := by
      rw [← U.ι.isOpenEmbedding.isInducing.isPreconnected_image, Scheme.Hom.comp_base,
        TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range,
        Scheme.Opens.range_ι, Set.inter_comm, hU]
      exact isPreconnected_connectedComponentIn
    let q := U.ι ≫ f
    have hsq : s ≫ q = Y.fromSpecResidueField (b y') := by
      rw [← Category.assoc, hs, Category.assoc, hσ, Category.comp_id]
    let s' : Spec (Y.residueField (b y')) ⟶ q.fiber (b y') :=
      pullback.lift s (𝟙 _) (by simp [hsq])
    have : Nonempty (q ⁻¹' {b y'}) :=
      ⟨q.fiberHomeo _ (s' (Nonempty.some inferInstance))⟩
    have : PreconnectedSpace (q ⁻¹' {b y'}) := isPreconnected_iff_preconnectedSpace.mp hq
    have : ConnectedSpace (q ⁻¹' {b y'}) := ⟨inferInstance⟩
    have : ConnectedSpace (q.fiber (b y')) :=
      (q.fiberHomeo _).connectedSpace_iff.mpr inferInstance
    have hgeom := GeometricallyConnected.of_connectedSpace_of_section
      (q.fiberToSpecResidueField (b y')) s' (pullback.lift_snd _ _ _)
    have : ConnectedSpace ((W.ι ≫ f').fiber y') :=
      hgeom.geometrically_connectedSpace _ _ _
        (isPullback_fiberToSpecResidueField_of_isPullback hW y')
    have hconn : _root_.IsConnected ((W.ι ≫ f') ⁻¹' {y'}) :=
      isConnected_iff_connectedSpace.mpr
        (((W.ι ≫ f').fiberHomeo y').connectedSpace_iff.mp this)
    have hmem (z) (hzU : a z ∈ U) (hz : f' z = y') :
        z ∈ W.ι '' ((W.ι ≫ f') ⁻¹' {y'}) := by
      obtain ⟨w, rfl⟩ : z ∈ Set.range W.ι := by
        rw [Scheme.Opens.range_ι]
        exact hzU
      exact ⟨w, by simpa using hz, rfl⟩
    refine (hconn.isPreconnected.image _ W.ι.continuous.continuousOn).subset_connectedComponentIn
      (hmem p (hp₁ ▸ hσU) hp₂) ?_ (hmem x' (hU.ge hx).1 rfl)
    rintro _ ⟨w, hw, rfl⟩
    simpa using hw
  · intro hx
    refine (isPreconnected_connectedComponentIn.image _
      a.continuous.continuousOn).subset_connectedComponentIn ?_ ?_
      ⟨x', hx, rfl⟩
    · exact ⟨p, mem_connectedComponentIn hp₂, hp₁⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ f' ⁻¹' {y'} := connectedComponentIn_subset _ _ hz
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hz'
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, h.w,
        Scheme.Hom.comp_apply, hz']

end AlgebraicGeometry
