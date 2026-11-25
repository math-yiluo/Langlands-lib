/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback

import WeilConjectures.AlgebraicGeometry.ClosedCoverFrameTransitions
import WeilConjectures.AlgebraicGeometry.GlueComponentReducedCoverSections
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.GlueComponentTransitionCocycle

/-! # ExistsGluedInvertible

Source: Stacks Project, Varieties Lemma 09NE. -/

@[expose] public section
universe u v
open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
-- Equality of transition coefficients suffices to glue the frame-preserving isomorphism.
private theorem nonempty_iso_of_common_transitions
    {X : Scheme.{u}} {κ : Type*} (U : κ → X.Opens) (hU : ⨆ p, U p = ⊤)
    {P Q : X.Modules} (e : ∀ p, Γ(P, U p)) (f : ∀ p, Γ(Q, U p))
    (he : ∀ p, IsFreeGenerator (e p)) (hf : ∀ p, IsFreeGenerator (f p))
    (r : ∀ p q, Γ(X, U p ⊓ U q))
    (hPe : ∀ p q, P.presheaf.map (homOfLE inf_le_left).op (e p) =
      r p q • P.presheaf.map (homOfLE inf_le_right).op (e q))
    (hQf : ∀ p q, Q.presheaf.map (homOfLE inf_le_left).op (f p) =
      r p q • Q.presheaf.map (homOfLE inf_le_right).op (f q)) :
    Nonempty (P ≅ Q) := by
  apply nonempty_iso_of_isFreeGenerator (e := e) (f := f) hU he _ hf
  intro p q W hp hq a b hab
  let c : Γ(X, W) := X.presheaf.map (homOfLE (le_inf hp hq)).op (r p q)
  have hP : P.presheaf.map (homOfLE hp).op (e p) =
      c • P.presheaf.map (homOfLE hq).op (e q) := by
    have h := congrArg (P.presheaf.map (homOfLE (le_inf hp hq)).op) (hPe p q)
    simpa only [map_smul, presheaf_map_homOfLE_map_homOfLE] using h
  have hQ : Q.presheaf.map (homOfLE hp).op (f p) =
      c • Q.presheaf.map (homOfLE hq).op (f q) := by
    have h := congrArg (Q.presheaf.map (homOfLE (le_inf hp hq)).op) (hQf p q)
    simpa only [map_smul, presheaf_map_homOfLE_map_homOfLE] using h
  have hc : a * c = b := ((he q).map hq).smul_left_injective (by
    simpa only [hP, smul_smul] using hab)
  rw [hQ, smul_smul, hc]

/-- Source: literature/stacks-project/varieties.tex, Varieties Lemma 09NE, proof.

Proof: The proved closed-cover frame construction chooses a point-indexed open cover,
free frames for each component module on the inverse images of its members, and units
on overlaps realizing all component frame changes. Distinct cover members overlap
only outside the union T of component intersections, and diagonal units are one.
Restrict frame relations to any smaller ambient open. Cancelling a free component
frame proves the inverse and cocycle identities after restriction to each component.
Off T the reduced-cover section bijection then proves these identities on Y; if all
indices coincide they follow from the diagonal units being one. Apply the stated
Cech transition gluing theorem to obtain N, free frames, and invertibility.
Pull the frames back to each component. They remain free and have the same transition
coefficients as the prescribed component frames. The proved common-transition
comparison glues their frame-preserving isomorphism, using the source library's
free-generator gluing theorem. Finally identify tensor pullback with the source
pullback by uniqueness of left adjoints to module pushforward. All constructions
include empty inverse-image opens. For Y empty the point-indexed cover is empty;
an empty component index family forces this case by hcover.
(blueprint: lem-sc-exists-glued-invertible) -/
theorem existsGluedInvertible
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ Y) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ)
    (hdiscrete : ∀ a b : ι, a ≠ b →
      DiscreteTopology ↥(Set.range (i a) ∩ Set.range (i b)))
    (M : ∀ a : ι, (Z a).Modules) [∀ a : ι, (M a).IsInvertible] :
    ∃ N : Y.Modules, N.IsInvertible ∧
      ∀ a : ι, Nonempty ((tensorPullback (i a)).obj N ≅ M a) := by
  classical
  obtain ⟨U, g, f, hU, hid, hoff, hf, hfg⟩ :=
    exists_closedCover_frame_transitions Z i hcover hdiscrete M
  let T : Set Y := ⋃ a : ι, ⋃ b : ι, ⋃ (_ : b ≠ a),
    Set.range (i a) ∩ Set.range (i b)
  have hsep := (glue_component_reduced_cover_sections Z i hcover).2.2.2.2
  let gW (p q : Y) (W : Y.Opens) (hp : W ≤ U p) (hq : W ≤ U q) : Γ(Y, W)ˣ :=
    Units.map (Y.presheaf.map (homOfLE (le_inf hp hq)).op).hom.toMonoidHom (g p q)
  have hrel (a : ι) (p q : Y) (W : Y.Opens) (hp : W ≤ U p) (hq : W ≤ U q) :
      (M a).presheaf.map (homOfLE ((i a).preimage_mono hp)).op (f a p) =
        (i a).app W (gW p q W hp hq).val •
          (M a).presheaf.map (homOfLE ((i a).preimage_mono hq)).op (f a q) := by
    have h := congrArg
      ((M a).presheaf.map (homOfLE ((i a).preimage_mono (le_inf hp hq))).op)
      (hfg a p q)
    simp only [map_smul, presheaf_map_homOfLE_map_homOfLE] at h
    have hn := congrArg (fun k : Γ(Y, U p ⊓ U q) ⟶ Γ(Z a, (i a) ⁻¹ᵁ W) ↦
      k (g p q).val) ((i a).naturality (homOfLE (le_inf hp hq)).op)
    simp only [ConcreteCategory.comp_apply] at hn
    change (i a).app W (Y.presheaf.map (homOfLE (le_inf hp hq)).op (g p q).val) =
      (Z a).presheaf.map (homOfLE ((i a).preimage_mono (le_inf hp hq))).op
        ((i a).app (U p ⊓ U q) (g p q).val) at hn
    rw [← hn] at h
    exact h
  have hcoc_off (p q r : Y) (W : Y.Opens) (hp : W ≤ U p) (hq : W ≤ U q)
      (hr : W ≤ U r) (hWT : (W : Set Y) ⊆ Tᶜ) :
      gW p r W hp hr = gW p q W hp hq * gW q r W hq hr := by
    apply Units.ext
    apply (hsep W hWT).injective
    funext a
    have h := hrel a p q W hp hq
    rw [hrel a q r W hq hr, smul_smul, hrel a p r W hp hr] at h
    have hc := ((hf a r).map ((i a).preimage_mono hr)).smul_left_injective h
    simpa only [Units.val_mul, map_mul] using hc
  have hcoc (p q r : Y) (W : Y.Opens) (hp : W ≤ U p) (hq : W ≤ U q)
      (hr : W ≤ U r) : gW p r W hp hr = gW p q W hp hq * gW q r W hq hr := by
    by_cases hpq : p = q
    · subst q
      by_cases hpr : p = r
      · subst r
        simp [gW, hid]
      · exact hcoc_off p p r W hp hq hr
          (fun x hx ↦ hoff p r hpr ⟨hp hx, hr hx⟩)
    · exact hcoc_off p q r W hp hq hr
        (fun x hx ↦ hoff p q hpq ⟨hp hx, hq hx⟩)
  obtain ⟨N, e, hN, he, heg, _⟩ :=
    exists_invertible_of_cech_transition U hU g hcoc
  refine ⟨N, hN, fun a ↦ ?_⟩
  let e' : ∀ p : Y, Γ((pullback (i a)).obj N, (i a) ⁻¹ᵁ U p) :=
    fun p ↦ pullbackSection (i a) (e p)
  have he' : ∀ p, IsFreeGenerator (e' p) :=
    fun p ↦ (he p).pullback_unit_app (i a)
  let r : ∀ p q : Y, Γ(Z a, (i a) ⁻¹ᵁ U p ⊓ (i a) ⁻¹ᵁ U q) :=
    fun p q ↦ (i a).app (U p ⊓ U q) (g p q).val
  have her : ∀ p q,
      ((pullback (i a)).obj N).presheaf.map (homOfLE inf_le_left).op (e' p) =
        r p q •
          ((pullback (i a)).obj N).presheaf.map (homOfLE inf_le_right).op (e' q) := by
    intro p q
    have h := congrArg (pullbackSection (i a)) (heg p q)
    simpa only [e', r, pullbackSection_map, pullbackSection_smul, Scheme.Hom.preimage_inf] using h
  obtain ⟨φ⟩ := nonempty_iso_of_common_transitions (fun p ↦ (i a) ⁻¹ᵁ U p)
    ((i a).iSup_preimage_eq_top hU) e' (f a) he' (hf a) r her (hfg a)
  let comparison : tensorPullback (i a) ≅ pullback (i a) :=
    Adjunction.leftAdjointUniq (nonempty_tensorPullbackAdjunction (i a)).some
      (pullbackPushforwardAdjunction (i a))
  exact ⟨comparison.app N ≪≫ φ⟩
end AlgebraicGeometry.Scheme.Modules
