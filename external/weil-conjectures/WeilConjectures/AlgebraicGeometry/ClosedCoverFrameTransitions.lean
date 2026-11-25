/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.AlgebraicGeometry.GlueComponentReducedCoverSections
import Mathlib.Topology.DiscreteSubset
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Component frames and transition units for a finite closed cover

Source: Stacks Project, Varieties Lemma 09NE, direct proof before gluing the line bundle.
-/

@[expose] public section

universe u v
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

private theorem freeGenerator_bot {X : Scheme.{u}} (M : X.Modules) :
    IsFreeGenerator (0 : Γ(M, ⊥)) := by
  intro W hW
  obtain rfl : W = ⊥ := le_bot_iff.mp hW
  have hM : Subsingleton Γ(M, ⊥) :=
    ⟨fun a b ↦ TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
      (fun _ : PEmpty.{1} ↦ ⊥) ⊥ (fun i ↦ i.elim) (fun _ hx ↦ hx.elim)
      a b (fun i ↦ i.elim)⟩
  have hR : Subsingleton Γ(X, ⊥) :=
    ⟨fun a b ↦ TopCat.Sheaf.eq_of_locally_eq' X.sheaf
      (fun _ : PEmpty.{1} ↦ ⊥) ⊥ (fun i ↦ i.elim) (fun _ hx ↦ hx.elim)
      a b (fun i ↦ i.elim)⟩
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

-- Trivialize all the component modules simultaneously around one ambient point.
private theorem exists_componentFrame_neighborhood
    {Y : Scheme.{u}} {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ Y) [∀ a : ι, IsClosedImmersion (i a)]
    (M : ∀ a : ι, (Z a).Modules) [∀ a : ι, (M a).IsInvertible]
    (y : Y) (D : Y.Opens) (hy : y ∈ D) :
    ∃ (U : Y.Opens), y ∈ U ∧ U ≤ D ∧
      ∃ f : ∀ a, Γ(M a, (i a) ⁻¹ᵁ U), ∀ a, IsFreeGenerator (f a) := by
  classical
  have hlocal (a : ι) : ∃ (V : Y.Opens), y ∈ V ∧
      ∃ e : Γ(M a, (i a) ⁻¹ᵁ V), IsFreeGenerator e := by
    by_cases ha : y ∈ Set.range (i a)
    · obtain ⟨z, rfl⟩ := ha
      have : SheafOfModules.IsInvertible.{u, u, u} (M a) :=
        IsInvertible.sheafOfModules_isInvertible (M a)
      obtain ⟨E, hz, _, e, he⟩ := exists_isFreeGenerator (M a) (x := z) (W := ⊤) (by trivial)
      obtain ⟨V, hV, hpre⟩ := (i a).isClosedEmbedding.isInducing.isOpen_iff.mp E.1.isOpen
      let V' : Y.Opens := ⟨V, hV⟩
      have hE : (i a) ⁻¹ᵁ V' = E.1 := TopologicalSpace.Opens.ext hpre
      refine ⟨V', ?_, ?_⟩
      · change i a z ∈ V
        exact hpre.ge hz
      · rw [hE]
        exact ⟨e, he⟩
    · let V : Y.Opens := ⟨(Set.range (i a))ᶜ, (i a).isClosedEmbedding.isClosed_range.isOpen_compl⟩
      have hV : (i a) ⁻¹ᵁ V = ⊥ := by
        ext z
        simp [V]
      refine ⟨V, ha, ?_⟩
      rw [hV]
      exact ⟨0, freeGenerator_bot (M a)⟩
  choose V hyV e he using hlocal
  let U : Y.Opens := D ⊓ ⨅ a, V a
  have hUa (a : ι) : U ≤ V a := inf_le_right.trans (iInf_le V a)
  refine ⟨U, ⟨hy, ?_⟩, inf_le_left, ?_⟩
  · change y ∈ ((⨅ a, V a : Y.Opens) : Set Y)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hyV
  · exact ⟨fun a ↦ (M a).presheaf.map (homOfLE ((i a).preimage_mono (hUa a))).op (e a),
      fun a ↦ (he a).map ((i a).preimage_mono (hUa a))⟩

/-- A finite closed cover with discrete intersections admits local component frames whose
changes of frame come from a single system of Čech transition units on the ambient scheme.
This statement constructs only opens, sections of the prescribed modules, and ring units;
it does not construct a module on the ambient scheme.

Source: Stacks Project, Varieties Lemma 09NE, direct proof, from the definition of `T`
through the construction of the transition functions on the three kinds of overlaps.
(blueprint: lem-sc-closed-cover-frame-transitions)

Proof: Let T be the union of intersections of distinct component images. Finiteness and
closedness make T closed. A finite union of closed discrete subspaces is discrete: at a
point of T, exclude the closed members not containing it and intersect neighborhoods
isolating it in the members containing it. For each point t of T choose U_t meeting T
only at t. Exclude component images not containing t. Shrink U_t further, finitely many
times, so each prescribed component module has a free generator on its inverse image.
For each point outside T use its open complement as the initial neighborhood and
again shrink to trivialize each component through the point and exclude the others.
These choices give a point-indexed open cover U and frames f on every component inverse
image, including the unique frame of the zero module on empty opens. Distinct chosen
opens overlap only outside T. On such overlaps the section identity of
lem-sc-glue-component-reduced-cover-sections identifies ambient functions with the
product of component functions. Unique frame-change coefficients on the components
are units; lift their values and inverse values by the section identity. Injectivity
shows the lifted values multiply to one, giving ambient units g with the asserted
frame relation. On a diagonal overlap put g = 1. The empty
scheme has the empty point-indexed cover, and all assertions are vacuous.
-/
theorem exists_closedCover_frame_transitions
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ Y) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ)
    (hdiscrete : ∀ a b : ι, a ≠ b →
      DiscreteTopology ↥(Set.range (i a) ∩ Set.range (i b)))
    (M : ∀ a : ι, (Z a).Modules) [∀ a : ι, (M a).IsInvertible] :
    let T : Set Y := ⋃ a : ι, ⋃ b : ι, ⋃ (_ : b ≠ a),
      Set.range (i a) ∩ Set.range (i b)
    ∃ (U : Y → Y.Opens) (g : ∀ p q : Y, Γ(Y, U p ⊓ U q)ˣ)
      (f : ∀ (a : ι) (p : Y), Γ(M a, (i a) ⁻¹ᵁ U p)),
      (⨆ p, U p = ⊤) ∧
      (∀ p, g p p = 1) ∧
      (∀ p q : Y, p ≠ q → (U p ⊓ U q : Set Y) ⊆ Tᶜ) ∧
      (∀ a p, IsFreeGenerator (f a p)) ∧
      (∀ a p q,
        (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_left)).op (f a p) =
          (i a).app (U p ⊓ U q) (g p q).val •
            (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_right)).op
              (f a q)) := by
  classical
  let T : Set Y := ⋃ a : ι, ⋃ b : ι, ⋃ (_ : b ≠ a),
    Set.range (i a) ∩ Set.range (i b)
  have hc (a b : ι) : IsClosed (Set.range (i a) ∩ Set.range (i b)) :=
    (i a).isClosedEmbedding.isClosed_range.inter (i b).isClosedEmbedding.isClosed_range
  have hcT : IsClosed T := isClosed_iUnion_of_finite (fun a ↦
    isClosed_iUnion_of_finite (fun b ↦ isClosed_iUnion_of_finite (fun _ ↦ hc a b)))
  have hdT : _root_.IsDiscrete T := .iUnion (fun a ↦ .iUnion (fun b ↦
    .iUnion (fun hba ↦ isDiscrete_iff_discreteTopology.mpr (hdiscrete a b (Ne.symm hba)))
      (fun _ ↦ hc a b))
    (fun b ↦ isClosed_iUnion_of_finite (fun _ ↦ hc a b)))
    (fun a ↦ isClosed_iUnion_of_finite (fun b ↦
      isClosed_iUnion_of_finite (fun _ ↦ hc a b)))
  have hlocal (y : Y) : ∃ (U : Y.Opens), y ∈ U ∧
      (U : Set Y) ∩ T ⊆ {y} ∧
      ∃ f : ∀ a, Γ(M a, (i a) ⁻¹ᵁ U), ∀ a, IsFreeGenerator (f a) := by
    have hD : ∃ D : Y.Opens, y ∈ D ∧ (D : Set Y) ∩ T ⊆ {y} := by
      by_cases hyT : y ∈ T
      · obtain ⟨D, hoD, hDT⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hdT y hyT
        refine ⟨⟨D, hoD⟩, ?_, hDT.le⟩
        have hy : y ∈ D ∩ T := hDT.ge (Set.mem_singleton y)
        exact hy.1
      · refine ⟨⟨Tᶜ, hcT.isOpen_compl⟩, hyT, ?_⟩
        intro x hx
        exact (hx.1 hx.2).elim
    obtain ⟨D, hyD, hDT⟩ := hD
    obtain ⟨U, hyU, hUD, f, hf⟩ := exists_componentFrame_neighborhood Z i M y D hyD
    exact ⟨U, hyU, fun x hx ↦ hDT ⟨hUD hx.1, hx.2⟩, f, hf⟩
  choose U hyU hUT f hf using hlocal
  have hU : ⨆ p, U p = ⊤ := top_unique (fun y _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩)
  have hoff (p q : Y) (hpq : p ≠ q) : (U p ⊓ U q : Set Y) ⊆ Tᶜ := by
    intro x hx hxT
    have hxp : x = p := hUT p ⟨hx.1, hxT⟩
    have hxq : x = q := hUT q ⟨hx.2, hxT⟩
    exact hpq (hxp.symm.trans hxq)
  have hsep := (glue_component_reduced_cover_sections Z i hcover).2.2.2.2
  have hunit (p q : Y) : ∃ c : Γ(Y, U p ⊓ U q)ˣ, (p = q → c = 1) ∧
      (∀ a, (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_left)).op
        (f p a) = (i a).app (U p ⊓ U q) c.val •
          (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_right)).op (f q a)) := by
    by_cases hpq : p = q
    · subst q
      exact ⟨1, fun _ ↦ rfl, fun a ↦ by simp⟩
    · have hp (a : ι) := (hf p a).map
        ((i a).preimage_mono (inf_le_left : U p ⊓ U q ≤ U p))
      have hq (a : ι) := (hf q a).map
        ((i a).preimage_mono (inf_le_right : U p ⊓ U q ≤ U q))
      have hu (a : ι) := (hq a).exists_unit_smul_eq (hp a)
      choose c hc using hu
      obtain ⟨s, hs⟩ := (hsep (U p ⊓ U q) (hoff p q hpq)).surjective (fun a ↦ (c a).val)
      obtain ⟨t, ht⟩ := (hsep (U p ⊓ U q) (hoff p q hpq)).surjective
        (fun a ↦ ((c a)⁻¹).val)
      have hs' (a : ι) : (i a).app (U p ⊓ U q) s = (c a).val := congrFun hs a
      have ht' (a : ι) : (i a).app (U p ⊓ U q) t = ((c a)⁻¹).val := congrFun ht a
      have hst : s * t = 1 := by
        apply (hsep (U p ⊓ U q) (hoff p q hpq)).injective
        funext a
        change (i a).app (U p ⊓ U q) (s * t) = (i a).app (U p ⊓ U q) 1
        rw [map_mul, hs', ht', map_one, Units.mul_inv]
      let g : Γ(Y, U p ⊓ U q)ˣ := ⟨s, t, hst, (mul_comm t s).trans hst⟩
      refine ⟨g, fun heq ↦ (hpq heq).elim, fun a ↦ ?_⟩
      rw [show (i a).app (U p ⊓ U q) g.val = (c a).val from hs' a]
      exact hc a
  choose g hdiag hfg using hunit
  exact ⟨U, g, fun a p ↦ f p a, hU, fun p ↦ hdiag p p rfl, hoff,
    fun a p ↦ hf p a, fun a p q ↦ hfg p q a⟩

end AlgebraicGeometry.Scheme.Modules
