/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
import WeilConjectures.AlgebraicGeometry.NormalizedComponentSectionCover

/-! # Normalized component frames and their Čech data

Source: Stacks Project, Varieties Lemma 09NE (lemma-glue-invertible-sheaves).
(blueprint: lem-sc-component-section-cech-data) -/

@[expose] public section

universe u v
open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

private theorem exists_transition_unit
    {Y : Scheme.{u}} {ι : Type v} (Z : ι → Scheme.{u}) (i : ∀ a, Z a ⟶ Y)
    (M : ∀ a, (Z a).Modules) {B C : Y.Opens}
    (mB : ∀ a, Γ(M a, (i a) ⁻¹ᵁ B)) (mC : ∀ a, Γ(M a, (i a) ⁻¹ᵁ C))
    (hmB : ∀ a, IsFreeGenerator (mB a)) (hmC : ∀ a, IsFreeGenerator (mC a))
    (hbij : Function.Bijective
      (fun r : Γ(Y, B ⊓ C) ↦ fun a ↦ ((i a).app (B ⊓ C)).hom r)) :
    ∃ g : Γ(Y, B ⊓ C)ˣ, ∀ a,
      (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_left)).op (mB a) =
        ((i a).app (B ⊓ C)).hom g.val •
          (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_right)).op (mC a) := by
  classical
  have hunit (a : ι) := ((hmC a).map ((i a).preimage_mono inf_le_right)).exists_unit_smul_eq
    ((hmB a).map ((i a).preimage_mono inf_le_left))
  choose g hg using hunit
  obtain ⟨r, hr⟩ := hbij.2 (fun a ↦ (g a).val)
  obtain ⟨r', hr'⟩ := hbij.2 (fun a ↦ (g a)⁻¹.val)
  have hrr' : r * r' = 1 := by
    apply hbij.1
    funext a
    have ha := congrFun hr a
    have ha' := congrFun hr' a
    dsimp only at ha ha'
    change ((i a).app (B ⊓ C)).hom (r * r') = ((i a).app (B ⊓ C)).hom 1
    rw [map_mul, map_one, ha, ha']
    exact (g a).val_inv
  refine ⟨⟨r, r', hrr', by rw [mul_comm, hrr']⟩, fun a ↦ ?_⟩
  have ha := congrFun hr a
  dsimp only at ha
  change _ = ((i a).app (B ⊓ C)).hom r • _
  rw [ha]
  exact hg a

private theorem component_app_map
    {Y X : Scheme.{u}} (i : X ⟶ Y) {V W : Y.Opens} (h : W ≤ V) (r : Γ(Y, V)) :
    (i.app W).hom (Y.presheaf.map (homOfLE h).op r) =
      X.presheaf.map (homOfLE (i.preimage_mono h)).op ((i.app V).hom r) := by
  exact congrArg (fun q ↦ q.hom r) (i.naturality (homOfLE h).op)

private theorem component_frame_transition_restrict
    {Y : Scheme.{u}} {ι : Type v} (Z : ι → Scheme.{u}) (i : ∀ a, Z a ⟶ Y)
    (M : ∀ a, (Z a).Modules) {κ : Type*} (U : κ → Y.Opens)
    (m : ∀ a b, Γ(M a, (i a) ⁻¹ᵁ U b)) (g : ∀ b c, Γ(Y, U b ⊓ U c)ˣ)
    (htrans : ∀ a b c,
      (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_left)).op (m a b) =
        ((i a).app (U b ⊓ U c)).hom (g b c).val •
          (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_right)).op (m a c))
    (a : ι) (b c : κ) (W : Y.Opens) (hb : W ≤ U b) (hc : W ≤ U c) :
    (M a).presheaf.map (homOfLE ((i a).preimage_mono hb)).op (m a b) =
      ((i a).app W).hom
        ((Y.presheaf.map (homOfLE (le_inf hb hc)).op).hom (g b c).val) •
        (M a).presheaf.map (homOfLE ((i a).preimage_mono hc)).op (m a c) := by
  have h := congrArg
    ((M a).presheaf.map (homOfLE ((i a).preimage_mono (le_inf hb hc))).op)
    (htrans a b c)
  simpa only [map_smul, presheaf_map_homOfLE_map_homOfLE, component_app_map] using h

private theorem exists_cech_of_component_frame_cover
    {Y : Scheme.{u}} {ι : Type v} (Z : ι → Scheme.{u}) (i : ∀ a, Z a ⟶ Y)
    (M : ∀ a, (Z a).Modules) (s : ∀ a, Γ(M a, ⊤))
    {κ : Type*} (U : κ → Y.Opens) (f : ∀ b, Γ(Y, U b))
    (m : ∀ a b, Γ(M a, (i a) ⁻¹ᵁ U b))
    (hm : ∀ a b, IsFreeGenerator (m a b))
    (hs : ∀ a b, (M a).presheaf.map (homOfLE le_top).op (s a) =
      ((i a).app (U b)).hom (f b) • m a b)
    (hbij : ∀ b c, b ≠ c → ∀ (W : Y.Opens), W ≤ U b → W ≤ U c →
      Function.Bijective (fun r : Γ(Y, W) ↦ fun a ↦ ((i a).app W).hom r)) :
    ∃ g : ∀ b c, Γ(Y, U b ⊓ U c)ˣ,
      (∀ b, g b b = 1) ∧
      (∀ b c (W : Y.Opens) (hb : W ≤ U b) (hc : W ≤ U c),
        Units.map (Y.presheaf.map (homOfLE (le_inf hc hb)).op).hom.toMonoidHom (g c b) =
          (Units.map (Y.presheaf.map (homOfLE (le_inf hb hc)).op).hom.toMonoidHom
            (g b c))⁻¹) ∧
      (∀ b c d (W : Y.Opens)
        (hb : W ≤ U b) (hc : W ≤ U c) (hd : W ≤ U d),
        Units.map (Y.presheaf.map (homOfLE (le_inf hb hd)).op).hom.toMonoidHom (g b d) =
          Units.map (Y.presheaf.map (homOfLE (le_inf hb hc)).op).hom.toMonoidHom (g b c) *
            Units.map (Y.presheaf.map (homOfLE (le_inf hc hd)).op).hom.toMonoidHom (g c d)) ∧
      (∀ a b c,
        (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_left)).op (m a b) =
          ((i a).app (U b ⊓ U c)).hom (g b c).val •
            (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_right)).op (m a c)) ∧
      ∀ b c, Y.presheaf.map (homOfLE inf_le_left).op (f b) * (g b c).val =
        Y.presheaf.map (homOfLE inf_le_right).op (f c) := by
  classical
  have hex (b c : κ) : ∃ g : Γ(Y, U b ⊓ U c)ˣ, ∀ a,
      (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_left)).op (m a b) =
        ((i a).app (U b ⊓ U c)).hom g.val •
          (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_right)).op (m a c) := by
    by_cases hbc : b = c
    · subst c
      refine ⟨1, fun a ↦ ?_⟩
      simp only [Units.val_one, map_one, one_smul]
    · exact exists_transition_unit Z i M (m · b) (m · c) (hm · b) (hm · c)
        (hbij b c hbc _ inf_le_left inf_le_right)
  let g (b c : κ) : Γ(Y, U b ⊓ U c)ˣ := if b = c then 1 else (hex b c).choose
  have hg : ∀ a b c,
      (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_left)).op (m a b) =
        ((i a).app (U b ⊓ U c)).hom (g b c).val •
          (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_right)).op (m a c) := by
    intro a b c
    by_cases hbc : b = c
    · subst c
      simp only [g, ite_eq_left rfl, Units.val_one, map_one, one_smul]
    · simpa only [g, ite_eq_right hbc] using (hex b c).choose_spec a
  have hid : ∀ b, g b b = 1 := fun b ↦ by simp only [g, ite_eq_left rfl]
  refine ⟨g, hid, ?_, ?_, hg, ?_⟩
  · intro b c W hb hc
    by_cases hbc : b = c
    · subst c
      simp only [hid, map_one, inv_one]
    · apply eq_inv_iff_mul_eq_one.mpr
      apply Units.ext
      apply (hbij b c hbc W hb hc).1
      funext a
      dsimp only
      simp only [Units.val_mul, Units.coe_map, Units.val_one, map_mul, map_one]
      apply ((hm a c).map ((i a).preimage_mono hc)).smul_left_injective
      dsimp only [RingHom.toMonoidHom]
      rw [mul_smul, one_smul]
      exact (congrArg
        (fun x ↦ ((i a).app W).hom
          ((Y.presheaf.map (homOfLE (le_inf hc hb)).op).hom (g c b).val) • x)
        (component_frame_transition_restrict Z i M U m g hg a b c W hb hc).symm).trans
          (component_frame_transition_restrict Z i M U m g hg a c b W hc hb).symm
  · intro b c d W hb hc hd
    have hcheck (hinj : Function.Injective
        (fun r : Γ(Y, W) ↦ fun a ↦ ((i a).app W).hom r)) :
        Units.map (Y.presheaf.map (homOfLE (le_inf hb hd)).op).hom.toMonoidHom (g b d) =
          Units.map (Y.presheaf.map (homOfLE (le_inf hb hc)).op).hom.toMonoidHom (g b c) *
            Units.map (Y.presheaf.map (homOfLE (le_inf hc hd)).op).hom.toMonoidHom
              (g c d) := by
      apply Units.ext
      apply hinj
      funext a
      dsimp only
      simp only [Units.val_mul, Units.coe_map, map_mul]
      apply ((hm a d).map ((i a).preimage_mono hd)).smul_left_injective
      dsimp only [RingHom.toMonoidHom]
      rw [mul_smul]
      exact (component_frame_transition_restrict Z i M U m g hg a b d W hb hd).symm.trans
        ((component_frame_transition_restrict Z i M U m g hg a b c W hb hc).trans
          (congrArg (fun x ↦ ((i a).app W).hom
            ((Y.presheaf.map (homOfLE (le_inf hb hc)).op).hom (g b c).val) • x)
            (component_frame_transition_restrict Z i M U m g hg a c d W hc hd)))
    by_cases hbc : b = c
    · subst c
      by_cases hbd : b = d
      · subst d
        simp only [hid, map_one, mul_one]
      · exact hcheck (hbij b d hbd W hb hd).1
    · exact hcheck (hbij b c hbc W hb hc).1
  · intro b c
    by_cases hbc : b = c
    · subst c
      simp only [hid, Units.val_one, mul_one]
    · apply (hbij b c hbc _ inf_le_left inf_le_right).1
      funext a
      dsimp only
      rw [map_mul]
      apply ((hm a c).map ((i a).preimage_mono inf_le_right)).smul_left_injective
      dsimp only [RingHom.toMonoidHom]
      rw [mul_smul, ← hg a b c]
      have hsb := congrArg
        ((M a).presheaf.map
          (homOfLE ((i a).preimage_mono (inf_le_left : U b ⊓ U c ≤ U b))).op) (hs a b)
      have hsc := congrArg
        ((M a).presheaf.map
          (homOfLE ((i a).preimage_mono (inf_le_right : U b ⊓ U c ≤ U c))).op) (hs a c)
      simp only [map_smul, presheaf_map_homOfLE_map_homOfLE] at hsb hsc
      rw [component_app_map (i a) (inf_le_left : U b ⊓ U c ≤ U b),
        component_app_map (i a) (inf_le_right : U b ⊓ U c ≤ U c)]
      exact hsb.symm.trans hsc

/-- Source: Stacks Project, Varieties Lemma 09NE, transition-function paragraphs and
final paragraph.

Proof: Take the normalized cover, component frames m, and scalar expressions f for s
from exists_normalized_component_section_cover. On a distinct overlap the component
structure-section map is bijective. Compare the two component frames by units. Lift
both the ratios and their inverses to functions r and r' on Y. Injectivity of the
comparison map proves r*r'=1, giving a unit g. Set every diagonal transition to 1.
Restrict the component frame equations to smaller opens using naturality. Cancellation
of a free generator proves the inverse and cocycle equations componentwise, and
injectivity descends them to Y. For a triple overlap use any unequal pair of indices
to obtain injectivity; when all three agree the equation follows from g_bb=1.
Restrict both expressions for the prescribed component section to the overlap,
substitute the frame transition, and cancel the second frame. Injectivity gives
f_b*g_bc=f_c. For a repeated index this equation is reflexive. These arguments also
work for empty overlaps, empty components, and the empty cover of an empty scheme.
No global module or section is constructed by this theorem.
(blueprint: lem-sc-component-section-cech-data) -/
theorem exists_component_section_cech_data
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ Y) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ)
    (hdiscrete : ∀ a b : ι, a ≠ b →
      DiscreteTopology ↥(Set.range (i a) ∩ Set.range (i b)))
    (M : ∀ a : ι, (Z a).Modules) [∀ a : ι, (M a).IsInvertible]
    (s : ∀ a : ι, Γ(M a, ⊤))
    (hs : ∀ a b : ι, a ≠ b → Set.range (i a) ∩ Set.range (i b) ⊆
      i a '' nonvanishingLocus (M a) (s a)) :
    ∃ (κ : Type (max u v)) (U : κ → Y.Opens)
      (g : ∀ b c, Γ(Y, U b ⊓ U c)ˣ) (f : ∀ b, Γ(Y, U b))
      (m : ∀ a b, Γ(M a, (i a) ⁻¹ᵁ U b)),
      (⨆ b, U b) = ⊤ ∧
      (∀ b, g b b = 1) ∧
      (∀ b c (W : Y.Opens) (hb : W ≤ U b) (hc : W ≤ U c),
        Units.map (Y.presheaf.map (homOfLE (le_inf hc hb)).op).hom.toMonoidHom (g c b) =
          (Units.map (Y.presheaf.map (homOfLE (le_inf hb hc)).op).hom.toMonoidHom
            (g b c))⁻¹) ∧
      (∀ b c d (W : Y.Opens)
        (hb : W ≤ U b) (hc : W ≤ U c) (hd : W ≤ U d),
        Units.map (Y.presheaf.map (homOfLE (le_inf hb hd)).op).hom.toMonoidHom (g b d) =
          Units.map (Y.presheaf.map (homOfLE (le_inf hb hc)).op).hom.toMonoidHom (g b c) *
            Units.map (Y.presheaf.map (homOfLE (le_inf hc hd)).op).hom.toMonoidHom (g c d)) ∧
      (∀ a b, IsFreeGenerator (m a b)) ∧
      (∀ a b c,
        (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_left)).op (m a b) =
          ((i a).app (U b ⊓ U c)).hom (g b c).val •
            (M a).presheaf.map (homOfLE ((i a).preimage_mono inf_le_right)).op (m a c)) ∧
      (∀ a b, (M a).presheaf.map (homOfLE le_top).op (s a) =
        ((i a).app (U b)).hom (f b) • m a b) ∧
      ∀ b c, Y.presheaf.map (homOfLE inf_le_left).op (f b) * (g b c).val =
        Y.presheaf.map (homOfLE inf_le_right).op (f c) := by
  classical
  obtain ⟨κ, U, f, m, hU, hm, hslocal, hbij⟩ :=
    exists_normalized_component_section_cover Z i hcover hdiscrete M s hs
  obtain ⟨g, hid, hinv, hcoc, htrans, hf⟩ :=
    exists_cech_of_component_frame_cover Z i M s U f m hm hslocal hbij
  exact ⟨κ, U, g, f, m, hU, hid, hinv, hcoc, hm, htrans, hslocal, hf⟩

end AlgebraicGeometry.Scheme.Modules
