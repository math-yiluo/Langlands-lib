/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.Fiber

/-!
# Base change of the fibre component containing a smooth section

Source: Stacks Project, Tag 055M.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

/-- In any ambient space, a component of a locally connected subspace is cut out by
an ambient open set. This uses Mathlib's openness of connected components and the
characterization of open sets for the induced topology. -/
private theorem exists_component_open {X : Type*} [TopologicalSpace X]
    (S : Set X) [LocallyConnectedSpace S] (x : X) :
    ∃ U : TopologicalSpace.Opens X, (U : Set X) ∩ S = connectedComponentIn S x := by
  by_cases hx : x ∈ S
  · obtain ⟨t, ht, hct⟩ := isOpen_induced_iff.mp
      (isOpen_connectedComponent (x := (⟨x, hx⟩ : S)))
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [connectedComponentIn_eq_image hx, ← hct, Set.image_preimage_eq_inter_range,
      Subtype.range_coe]
    rfl
  · exact ⟨⊥, by simp [connectedComponentIn_eq_empty hx]⟩

/-- The component of the section in a fibre of a smooth morphism is preserved by any
cartesian base change equipped with the compatible section.

Source: Stacks Project, Tag 055M (Lemma 37.29.2).
Proof: for p' in P', put t' = g'(p') and t = b(t'). The cartesian square identifies
P'_{t'} with P_t ×_{κ(t)} κ(t'), and the section compatibility identifies the distinguished
point with the base change of σ(t). The component C of σ(t) is a connected smooth
κ(t)-scheme with a κ(t)-rational point; it is geometrically connected by Varieties,
Lemma 33.7.14. Here fibres are locally noetherian, and their components are open and
closed, since g is smooth and quasi-compact. Thus C × κ(t') is a connected open and
closed subscheme containing σ'(t'), so it lies in that point's component. Conversely
the continuous projection maps the component of σ'(t') to a connected subset containing
σ(t), hence into C. These inclusions give equality of the component and the inverse
image of C. Finally the underlying space of a scheme fibre maps homeomorphically onto
the topological fibre; under this identification the equality is the displayed iff.
This argument applies at each p', without a noetherian assumption on the bases.

(blueprint: lem-sbc-smooth-section-component-noetherian-model-components) -/
theorem Smooth.section_component_iff_of_isPullback {P T P' T' : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T)
    (g' : P' ⟶ T') (σ' : T' ⟶ P') (a : P' ⟶ P) (b : T' ⟶ T)
    (sq : IsPullback a g' g b) (hσ' : σ' ≫ g' = 𝟙 T') (hsec : σ' ≫ a = b ≫ σ) :
    ∀ p' : P', (p' ∈ connectedComponentIn (g' ⁻¹' {g' p'}) (σ' (g' p'))) ↔
      a p' ∈ connectedComponentIn (g ⁻¹' {g (a p')}) (σ (g (a p'))) := by
  intro x'
  set y' := g' x'
  set p := σ' y'
  have hfx : g (a x') = b y' := by
    rw [← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]
  have hp₁ : a p = σ (b y') := by
    rw [← Scheme.Hom.comp_apply, hsec, Scheme.Hom.comp_apply]
  have hp₂ : g' p = y' := by
    rw [← Scheme.Hom.comp_apply, hσ']
    rfl
  have hσy (y : T) : g (σ y) = y := by
    rw [← Scheme.Hom.comp_apply, hσ]
    rfl
  rw [hfx]
  apply Iff.symm
  constructor
  · intro hx
    obtain ⟨Uₜ, hU⟩ := exists_component_open (g ⁻¹' {b y'}) (σ (b y'))
    let U : P.Opens := Uₜ
    have hσU : σ (b y') ∈ U := (hU.ge (mem_connectedComponentIn (hσy _))).1
    let W := a ⁻¹ᵁ U
    have hW := (isPullback_morphismRestrict a U).paste_vert sq
    have hs := IsOpenImmersion.lift_fac U.ι (T.fromSpecResidueField (b y') ≫ σ) (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
      exact hσU)
    have hq : _root_.IsPreconnected ((U.ι ≫ g) ⁻¹' {b y'}) := by
      rw [← U.ι.isOpenEmbedding.isInducing.isPreconnected_image, Scheme.Hom.comp_base,
        TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range,
        Scheme.Opens.range_ι, Set.inter_comm, hU]
      exact isPreconnected_connectedComponentIn
    let s := IsOpenImmersion.lift U.ι (T.fromSpecResidueField (b y') ≫ σ) (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
      exact hσU)
    have hsq : s ≫ (U.ι ≫ g) = T.fromSpecResidueField (b y') := by
      rw [← Category.assoc, hs, Category.assoc, hσ, Category.comp_id]
    let s' : Spec (T.residueField (b y')) ⟶ (U.ι ≫ g).fiber (b y') :=
      pullback.lift s (𝟙 _) (by simp [hsq])
    have : Nonempty ((U.ι ≫ g) ⁻¹' {b y'}) :=
      ⟨(U.ι ≫ g).fiberHomeo _ (s' (Nonempty.some inferInstance))⟩
    have : PreconnectedSpace ((U.ι ≫ g) ⁻¹' {b y'}) :=
      isPreconnected_iff_preconnectedSpace.mp hq
    have : ConnectedSpace ((U.ι ≫ g) ⁻¹' {b y'}) := ⟨inferInstance⟩
    have : ConnectedSpace ((U.ι ≫ g).fiber (b y')) :=
      ((U.ι ≫ g).fiberHomeo _).connectedSpace_iff.mpr inferInstance
    have : ConnectedSpace ((W.ι ≫ g').fiber y') :=
      (GeometricallyConnected.of_connectedSpace_of_section
        ((U.ι ≫ g).fiberToSpecResidueField (b y')) s'
        (pullback.lift_snd _ _ _)).geometrically_connectedSpace _ _ _
        (isPullback_fiberToSpecResidueField_of_isPullback hW y')
    have hconn : _root_.IsConnected ((W.ι ≫ g') ⁻¹' {y'}) :=
      isConnected_iff_connectedSpace.mpr
        (((W.ι ≫ g').fiberHomeo y').connectedSpace_iff.mp this)
    have hmem (z) (hzU : a z ∈ U) (hz : g' z = y') :
        z ∈ W.ι '' ((W.ι ≫ g') ⁻¹' {y'}) := by
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
      a.continuous.continuousOn).subset_connectedComponentIn ?_ ?_ ⟨x', hx, rfl⟩
    · exact ⟨p, mem_connectedComponentIn hp₂, hp₁⟩
    · rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ g' ⁻¹' {y'} := connectedComponentIn_subset _ _ hz
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hz'
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, sq.w,
        Scheme.Hom.comp_apply, hz']

end AlgebraicGeometry
