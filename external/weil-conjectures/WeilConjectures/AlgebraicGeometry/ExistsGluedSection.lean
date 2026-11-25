/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

import WeilConjectures.AlgebraicGeometry.ComponentSectionCechData
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.GlueComponentTransitionCocycle

/-! # ExistsGluedSection

Source: Stacks Project, Varieties Lemma 09NE. -/

@[expose] public section
universe u v
open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

private theorem matching_frame_relations
    {X : Scheme.{u}} {κ : Type*} (U : κ → X.Opens)
    {P Q : X.Modules} (e : ∀ b, Γ(P, U b)) (m : ∀ b, Γ(Q, U b))
    (he : ∀ b, IsFreeGenerator (e b))
    (g : ∀ b c, Γ(X, U b ⊓ U c))
    (hP : ∀ b c, P.presheaf.map (homOfLE inf_le_left).op (e b) =
      g b c • P.presheaf.map (homOfLE inf_le_right).op (e c))
    (hQ : ∀ b c, Q.presheaf.map (homOfLE inf_le_left).op (m b) =
      g b c • Q.presheaf.map (homOfLE inf_le_right).op (m c)) :
    ∀ b c (W : X.Opens) (hb : W ≤ U b) (hc : W ≤ U c) (r t : Γ(X, W)),
      r • P.presheaf.map (homOfLE hb).op (e b) =
        t • P.presheaf.map (homOfLE hc).op (e c) →
      r • Q.presheaf.map (homOfLE hb).op (m b) =
        t • Q.presheaf.map (homOfLE hc).op (m c) := by
  intro b c W hb hc r t h
  have hP' := congrArg (P.presheaf.map (homOfLE (le_inf hb hc)).op) (hP b c)
  have hQ' := congrArg (Q.presheaf.map (homOfLE (le_inf hb hc)).op) (hQ b c)
  simp only [map_smul, presheaf_map_homOfLE_map_homOfLE] at hP' hQ'
  have hr : r * X.presheaf.map (homOfLE (le_inf hb hc)).op (g b c) = t := by
    apply ((he c).map hc).smul_left_injective
    simpa only [mul_smul, ← hP'] using h
  rw [hQ', ← mul_smul, hr]

private theorem exists_iso_preserving_frame_relations
    {X : Scheme.{u}} {κ : Type*} {U : κ → X.Opens} {P Q : X.Modules}
    (e : ∀ b, Γ(P, U b)) (m : ∀ b, Γ(Q, U b))
    (hU : (⨆ b, U b) = ⊤) (he : ∀ b, IsFreeGenerator (e b))
    (hm : ∀ b, IsFreeGenerator (m b))
    (hc : ∀ b c (W : X.Opens) (hb : W ≤ U b) (hc : W ≤ U c) (r t : Γ(X, W)),
      r • P.presheaf.map (homOfLE hb).op (e b) =
        t • P.presheaf.map (homOfLE hc).op (e c) →
      r • Q.presheaf.map (homOfLE hb).op (m b) =
        t • Q.presheaf.map (homOfLE hc).op (m c)) :
    ∃ φ : P ≅ Q, ∀ (V : X.Opens) (x : Γ(P, V)),
      IsGlueValue e m x (φ.hom.app V x) := by
  have hc' : ∀ b c (W : X.Opens) (hb : W ≤ U b) (hc : W ≤ U c) (r t : Γ(X, W)),
      r • Q.presheaf.map (homOfLE hb).op (m b) =
        t • Q.presheaf.map (homOfLE hc).op (m c) →
      r • P.presheaf.map (homOfLE hb).op (e b) =
        t • P.presheaf.map (homOfLE hc).op (e c) := by
    intro b c W hb hWc r t h
    have h' := hc b c W hb hWc r _
      (((he c).map hWc).coeff_smul
        (r • P.presheaf.map (homOfLE hb).op (e b))).symm
    rw [← ((he c).map hWc).coeff_smul (r • P.presheaf.map (homOfLE hb).op (e b))]
    congr 1
    exact ((hm c).map hWc).smul_left_injective (h'.symm.trans h)
  let φ : P ≅ Q :=
    { hom := glueHom hU he hc
      inv := glueHom hU hm hc'
      hom_inv_id := by
        refine hom_ext _ _ fun V ↦ ?_
        ext x
        exact (isGlueValue_glueHom_app hU hm hc' _).unique hU hm
          ((isGlueValue_glueHom_app hU he hc x).symm he hm)
      inv_hom_id := by
        refine hom_ext _ _ fun V ↦ ?_
        ext x
        exact (isGlueValue_glueHom_app hU he hc _).unique hU he
          ((isGlueValue_glueHom_app hU hm hc' x).symm hm he) }
  exact ⟨φ, fun _ x ↦ isGlueValue_glueHom_app hU he hc x⟩

/-- Source: literature/stacks-project/varieties.tex, Varieties Lemma 09NE, final assertion.

Proof: As in the construction of the glued module, choose neighborhoods of points of
T meeting T only at the chosen point. At such a point all sections on incident
components generate their line bundles by the nonvanishing hypothesis. Shrink the
neighborhood and normalize all frames to carry the prescribed sections to 1. Off T
use arbitrary trivializing frames. The reduced-cover section identity transfers the
frame changes on overlaps to units on Y. Glue the trivial modules with these transition
units. On the neighborhoods of T take the section 1; elsewhere take the expression of
the prescribed section in its component frame. These local expressions agree under the
transition maps because those maps are frame changes; the sheaf axiom produces t.
The component frame isomorphisms glue to the asserted pullback isomorphisms, under which
t restricts to s. The restriction is the unit of the tensor-pullback adjunction as in
the target statement. If T is empty the disjoint components simply glue independently.
(blueprint: lem-sc-exists-glued-section) -/
theorem existsGluedSection
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (Z : ι → Scheme.{u}) (i : ∀ a : ι, Z a ⟶ Y) [∀ a : ι, IsClosedImmersion (i a)]
    (hcover : (⋃ a : ι, Set.range (i a)) = Set.univ)
    (hdiscrete : ∀ a b : ι, a ≠ b →
      DiscreteTopology ↥(Set.range (i a) ∩ Set.range (i b)))
    (M : ∀ a : ι, (Z a).Modules) [∀ a : ι, (M a).IsInvertible]
    (s : ∀ a : ι, Γ(M a, ⊤))
    (hs : ∀ a b : ι, a ≠ b → Set.range (i a) ∩ Set.range (i b) ⊆
      i a '' nonvanishingLocus (M a) (s a)) :
    let res : ∀ (N : Y.Modules) (a : ι), Γ(N, ⊤) → Γ((tensorPullback (i a)).obj N, ⊤) :=
      fun N a t ↦ ((Classical.choose (exists_tensorPullbackAdjunction (i a))).unit.app N).val.app
        (op ⊤) t
    ∃ (N : Y.Modules) (t : Γ(N, ⊤)), N.IsInvertible ∧
      ∀ a : ι, ∃ e : (tensorPullback (i a)).obj N ≅ M a,
        e.hom.val.app (op ⊤) (res N a t) = s a := by
  classical
  dsimp only
  obtain ⟨κ, U, g, f, m, hU, -, -, hcoc, hm, htrans, hslocal, hf⟩ :=
    exists_component_section_cech_data Z i hcover hdiscrete M s hs
  obtain ⟨N, e, hN, he, hetrans, _⟩ :=
    exists_invertible_of_cech_transition U hU g hcoc
  have hfe : TopCat.Presheaf.IsCompatible N.presheaf U (fun b ↦ f b • e b) := by
    intro b c
    change N.presheaf.map (homOfLE inf_le_left).op (f b • e b) =
      N.presheaf.map (homOfLE inf_le_right).op (f c • e c)
    rw [map_smul, map_smul, hetrans b c, ← mul_smul, hf b c]
  obtain ⟨t, ht, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨N.presheaf, N.isSheaf⟩
    U ⊤ (fun _ ↦ homOfLE le_top) hU.ge (fun b ↦ f b • e b) hfe
  refine ⟨N, t, hN, ?_⟩
  intro a
  let P := (pullback (i a)).obj N
  let E : ∀ b, Γ(P, (i a) ⁻¹ᵁ U b) := fun b ↦ pullbackSection (i a) (e b)
  have hE : ∀ b, IsFreeGenerator (E b) := fun b ↦ (he b).pullback_unit_app (i a)
  have hU' : (⨆ b, (i a) ⁻¹ᵁ U b) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  let q : ∀ b c, Γ(Z a, ((i a) ⁻¹ᵁ U b) ⊓ ((i a) ⁻¹ᵁ U c)) :=
    fun b c ↦ ((i a).app (U b ⊓ U c)).hom (g b c).val
  have hEtrans : ∀ b c,
      P.presheaf.map (homOfLE inf_le_left).op (E b) =
        q b c • P.presheaf.map (homOfLE inf_le_right).op (E c) := by
    intro b c
    change P.presheaf.map (homOfLE ((i a).preimage_mono inf_le_left)).op
      (pullbackSection (i a) (e b)) =
      ((i a).app (U b ⊓ U c)).hom (g b c).val •
        P.presheaf.map (homOfLE ((i a).preimage_mono inf_le_right)).op
          (pullbackSection (i a) (e c))
    rw [← pullbackSection_map (i a) (inf_le_left : U b ⊓ U c ≤ U b),
      ← pullbackSection_map (i a) (inf_le_right : U b ⊓ U c ≤ U c),
      hetrans b c, pullbackSection_smul]
  have hmtrans : ∀ b c,
      (M a).presheaf.map (homOfLE inf_le_left).op (m a b) =
        q b c • (M a).presheaf.map (homOfLE inf_le_right).op (m a c) := htrans a
  obtain ⟨φ, hφ⟩ := exists_iso_preserving_frame_relations E (m a) hU' hE (hm a)
    (matching_frame_relations _ E (m a) hE q hEtrans hmtrans)
  let adj := Classical.choose (exists_tensorPullbackAdjunction (i a))
  let ψ := (adj.leftAdjointUniq (pullbackPushforwardAdjunction (i a))).app N
  refine ⟨ψ ≪≫ φ, ?_⟩
  have hu := Adjunction.unit_leftAdjointUniq_hom_app adj
    (pullbackPushforwardAdjunction (i a)) N
  have hut := congrArg (fun k : N ⟶ (pushforward (i a)).obj P ↦ k.app ⊤ t) hu
  change φ.hom.app ⊤ (ψ.hom.app ⊤ ((adj.unit.app N).app ⊤ t)) = s a
  have hunit : ψ.hom.app ⊤ ((adj.unit.app N).app ⊤ t) =
      pullbackSection (i a) t := hut
  rw [hunit]
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨(M a).presheaf, (M a).isSheaf⟩
    (fun b ↦ (i a) ⁻¹ᵁ U b) ⊤ (fun _ ↦ homOfLE le_top) hU'.ge
  intro b
  change (M a).presheaf.map (homOfLE le_top).op
      (φ.hom.app ⊤ (pullbackSection (i a) t)) =
    (M a).presheaf.map (homOfLE le_top).op (s a)
  rw [hslocal a b]
  have hlocal : ((i a).app (U b)).hom (f b) • E b =
      P.presheaf.map (homOfLE le_top).op (pullbackSection (i a) t) := by
    change ((i a).app (U b)).hom (f b) • pullbackSection (i a) (e b) =
      P.presheaf.map (homOfLE ((i a).preimage_mono (le_top : U b ≤ ⊤))).op
        (pullbackSection (i a) t)
    rw [← pullbackSection_smul, ← ht b, pullbackSection_map]
  simpa only [presheaf_map_id_apply] using
    hφ ⊤ (pullbackSection (i a) t) b _ le_top le_rfl
      (((i a).app (U b)).hom (f b))
      (by simpa only [presheaf_map_id_apply] using hlocal)
end AlgebraicGeometry.Scheme.Modules
