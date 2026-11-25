/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.GlueComponentTransitionCocycle
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # A line bundle and two sections from reciprocal local functions

Source: Stacks Project, Varieties Lemma 09NB, cocycle and two-section construction.
(blueprint: lem-sc-reciprocal-cover-line-bundle)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

private theorem exists_reciprocal_frames
    (X : Scheme.{u}) (U V : X.Opens) (f : Γ(X, U)) (g : Γ(X, V))
    (hcover : U ⊔ V = ⊤)
    (hinv : X.presheaf.map (homOfLE inf_le_left).op f *
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op g = 1) :
    ∃ (L : X.Modules) (eU : Γ(L, U)) (eV : Γ(L, V)),
      L.IsInvertible ∧ IsFreeGenerator eU ∧ IsFreeGenerator eV ∧
      L.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op eU =
        X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op g •
          L.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op eV := by
  let c : Γ(X, U ⊓ V)ˣ :=
    ⟨X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op g,
      X.presheaf.map (homOfLE inf_le_left).op f, by rw [mul_comm]; exact hinv, hinv⟩
  let A : Bool → X.Opens := fun a ↦ if a then V else U
  let q : ∀ a b, Γ(X, A a ⊓ A b)ˣ := fun a b ↦
    match a, b with
    | false, false => 1
    | false, true => c
    | true, false =>
      Units.map (X.presheaf.map (eqToHom (inf_comm V U)).op).hom.toMonoidHom c⁻¹
    | true, true => 1
  have hA : ⨆ a, A a = ⊤ := by
    rw [← hcover]
    apply le_antisymm
    · refine iSup_le fun a ↦ ?_
      cases a
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup A false) (le_iSup A true)
  have hrestrict {P Q W : X.Opens} (i : Q ⟶ P) (j : W ⟶ Q)
      (z : Γ(X, P)ˣ) :
      Units.map (X.presheaf.map j.op).hom.toMonoidHom
          (Units.map (X.presheaf.map i.op).hom.toMonoidHom z) =
        Units.map (X.presheaf.map (j ≫ i).op).hom.toMonoidHom z := by
    apply Units.ext
    exact Scheme.presheaf_map_map_apply i j z.val
  have hi : ∀ a b (W : X.Opens) (ha : W ≤ A a) (hb : W ≤ A b),
      Units.map (X.presheaf.map (homOfLE (le_inf hb ha)).op).hom.toMonoidHom (q b a) =
        (Units.map (X.presheaf.map (homOfLE (le_inf ha hb)).op).hom.toMonoidHom
          (q a b))⁻¹ := by
    intro a b W ha hb
    cases a <;> cases b
    · simp [q]
    · simp only [q, map_inv]
      congr 1
      exact hrestrict (eqToHom (inf_comm V U)) (homOfLE (le_inf hb ha)) c
    · simp only [q, map_inv, inv_inv]
      symm
      exact hrestrict (eqToHom (inf_comm V U)) (homOfLE (le_inf ha hb)) c
    · simp [q]
  have hc : ∀ a b d (W : X.Opens)
      (ha : W ≤ A a) (hb : W ≤ A b) (hd : W ≤ A d),
      Units.map (X.presheaf.map (homOfLE (le_inf ha hd)).op).hom.toMonoidHom (q a d) =
        Units.map (X.presheaf.map (homOfLE (le_inf ha hb)).op).hom.toMonoidHom (q a b) *
          Units.map (X.presheaf.map (homOfLE (le_inf hb hd)).op).hom.toMonoidHom
            (q b d) := by
    intro a b d W ha hb hd
    cases a <;> cases b <;> cases d
    all_goals try simp only [q, map_one, one_mul, mul_one]
    · rw [hi false true W ha hb]
      simp [q]
    · rw [hi false true W hb ha]
      simp [q]
  obtain ⟨L, e, hL, he, htrans, -⟩ :=
    exists_invertible_of_cech_transition A hA q hc
  exact ⟨L, e false, e true, hL, he false, he true, htrans false true⟩

private theorem exists_section_of_pair {X : Scheme.{u}} (M : X.Modules)
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) (a : Γ(M, U)) (b : Γ(M, V))
    (hab : M.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a =
      M.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op b) :
    ∃ σ : Γ(M, ⊤), M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op σ = a ∧
      M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ = b := by
  let A : Bool → X.Opens := fun i ↦ if i then V else U
  let z : ∀ i, Γ(M, A i) := fun i ↦ match i with
    | false => a
    | true => b
  have hA : ⊤ ≤ ⨆ i, A i := by
    rw [← hcover]
    exact sup_le (le_iSup A false) (le_iSup A true)
  have hz : TopCat.Presheaf.IsCompatible M.presheaf A z := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact hab
    · have h := congrArg
        (M.presheaf.map (eqToHom (inf_comm V U)).op) hab.symm
      simp only [presheaf_map_map_apply] at h
      convert h using 1 <;> congr 2
    · rfl
  obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩
    A ⊤ (fun _ ↦ homOfLE le_top) hA z hz
  exact ⟨σ, hσ false, hσ true⟩

private noncomputable def sectionOfTop {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) :
    M.sections :=
  ⟨fun W ↦ M.presheaf.map (homOfLE (le_top : W.unop ≤ ⊤)).op σ, by
    intro W Z i
    change M.presheaf.map i.unop.op
      (M.presheaf.map (homOfLE (le_top : W.unop ≤ ⊤)).op σ) = _
    rw [presheaf_map_map_apply]
    congr 2⟩

private theorem sectionOfTop_top {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) :
    (sectionOfTop M σ).val (Opposite.op ⊤) = σ :=
  presheaf_map_id_apply _ _

/-- Reciprocal local functions glue two trivial line bundles and two global sections.
This construction requires neither dimension nor separatedness nor an affine open.

Source: Stacks Project, Varieties Lemma 09NB (varieties-lemma-find-globally-generated),
proof, cocycle construction and the two displayed sections.
(blueprint: lem-sc-reciprocal-cover-line-bundle).

Proof: On U intersect V, the restrictions of f and g multiply to 1. Use the unit g
as the transition from the frame e_U to e_V, so e_U = g e_V. Use its inverse for
the reversed overlap and identity transitions on equal indices. The two-open Cech
identities follow by cancellation of inverse units. Glue using the Cech transition
lemma, obtaining an invertible L with these local frames. The pairs (e_U, g e_V)
and (f e_U, e_V) agree on the overlap, hence glue by the sheaf axiom to s and t.
Restriction of global sections to all opens turns these into elements of L.sections.
The section s is a free generator on U. On V its nonvanishing locus is D(g),
because a coefficient times a local frame has nonzero residue exactly when that
coefficient is a unit in the local ring. Since D(g) = U intersect V, the cover gives
X_s = U. Likewise t is a free generator on V, so V is contained in X_t.
For an empty chart the unique sections glue and the same argument applies.
-/
theorem exists_line_bundle_sections_of_reciprocal_cover
    (X : Scheme.{u}) (U V : X.Opens) (f : Γ(X, U)) (g : Γ(X, V))
    (hcover : U ⊔ V = ⊤)
    (hinv : X.presheaf.map (homOfLE inf_le_left).op f *
      X.presheaf.map (homOfLE inf_le_right).op g = 1)
    (hlocus : X.basicOpen g = U ⊓ V) :
    ∃ (L : X.Modules) (s t : L.sections), L.IsInvertible ∧
      nonvanishingLocus L (s.val (Opposite.op ⊤)) = (U : Set X) ∧
      (V : Set X) ⊆ nonvanishingLocus L (t.val (Opposite.op ⊤)) := by
  obtain ⟨L, eU, eV, hL, heU, heV, htrans⟩ :=
    exists_reciprocal_frames X U V f g hcover hinv
  have hscompat : L.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op eU =
      L.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op (g • eV) := by
    rw [map_smul]
    exact htrans
  have htcompat : L.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (f • eU) =
      L.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op eV := by
    rw [map_smul, htrans, ← mul_smul, hinv, one_smul]
  obtain ⟨σ, hσU, hσV⟩ := exists_section_of_pair L U V hcover eU (g • eV) hscompat
  obtain ⟨τ, hτU, hτV⟩ := exists_section_of_pair L U V hcover (f • eU) eV htcompat
  let : L.IsInvertible := hL
  refine ⟨L, sectionOfTop L σ, sectionOfTop L τ, hL, ?_, ?_⟩
  · rw [sectionOfTop_top]
    apply Set.ext
    intro x
    rw [mem_nonvanishingLocus_iff_generatesAt]
    constructor
    · intro hx
      have hxcover : x ∈ U ∨ x ∈ V := by
        change x ∈ U ⊔ V
        rw [hcover]
        trivial
      rcases hxcover with hxU | hxV
      · exact hxU
      · have hxg := (generatesAt_iff_mem_basicOpen heV hσV hxV).mp hx
        rw [hlocus] at hxg
        exact hxg.1
    · intro hxU
      exact ⟨U, hxU, hσU ▸ heU⟩
  · rw [sectionOfTop_top]
    intro x hxV
    rw [mem_nonvanishingLocus_iff_generatesAt]
    exact ⟨V, hxV, hτV ▸ heV⟩

end AlgebraicGeometry.Scheme.Modules
