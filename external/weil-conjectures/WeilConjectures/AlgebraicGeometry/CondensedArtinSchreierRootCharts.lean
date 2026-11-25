/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Section
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Root-labelled splitting charts of an Artin–Schreier cover -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem geometric_point_at (Z : Scheme.{u}) (z : Z) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (w : Spec (.of Ω) ⟶ Z), w default = z := by
  let K := Z.residueField z
  let Ω := AlgebraicClosure K
  let w : Spec (.of Ω) ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ Z.fromSpecResidueField z
  exact ⟨Ω, inferInstance, inferInstance, w, Z.fromSpecResidueField_apply z _⟩

private theorem root_sheets_colimit
    {X Y T : Scheme.{u}} (π : Y ⟶ X) [Etale π]
    (G : Type v) [Finite G] (σ : G → (Y ⟶ Y))
    (hσ : ∀ a, σ a ≫ π = π)
    (htrans : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s t : Spec (.of Ω) ⟶ Y), s ≫ π = t ≫ π →
        ∃! a : G, t = s ≫ σ a)
    (x : T ⟶ X) (s : T ⟶ Y) (hs : s ≫ π = x) :
    Nonempty (IsColimit (Cofan.mk (pullback π x)
      (fun a : G ↦ pullback.lift (s ≫ σ a) (𝟙 T)
        (by rw [Category.assoc, hσ a, hs, Category.id_comp])))) := by
  classical
  let t (a : G) : T ⟶ pullback π x :=
    pullback.lift (s ≫ σ a) (𝟙 T)
      (by rw [Category.assoc, hσ a, hs, Category.id_comp])
  have ht (a : G) : t a ≫ pullback.snd π x = 𝟙 T := pullback.lift_snd _ _ _
  let (a : G) : IsOpenImmersion (t a) :=
    IsOpenImmersion.of_section_of_etale (pullback.snd π x) (t a) (ht a)
  apply nonempty_isColimit_cofanMk_of t
  · apply top_unique
    intro z hz
    obtain ⟨Ω, hΩ, halg, w, hw⟩ := geometric_point_at (pullback π x) z
    let : Field Ω := hΩ
    let : IsAlgClosed Ω := halg
    let l : Spec (.of Ω) ⟶ T := w ≫ pullback.snd π x
    have hbase : (l ≫ s) ≫ π = (w ≫ pullback.fst π x) ≫ π := by
      rw [Category.assoc, hs]
      simpa only [l, Category.assoc] using
        congrArg (fun k ↦ w ≫ k) (pullback.condition (f := π) (g := x)).symm
    obtain ⟨a, ha, -⟩ := htrans Ω (l ≫ s) (w ≫ pullback.fst π x) hbase
    have he : l ≫ t a = w := by
      apply pullback.hom_ext
      · simpa only [t, Category.assoc, pullback.lift_fst] using ha.symm
      · simp only [t, Category.assoc, pullback.lift_snd, Category.comp_id, l]
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨a, l default, ?_⟩
    change (l ≫ t a) default = z
    rw [he, hw]
  · intro a b hab
    change Disjoint (t a).opensRange (t b).opensRange
    rw [disjoint_iff]
    apply bot_unique
    rintro z ⟨⟨za, hza⟩, ⟨zb, hzb⟩⟩
    obtain ⟨z', -, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := t a) (g := t b) za zb (hza.trans hzb.symm)
    obtain ⟨Ω, hΩ, halg, w, -⟩ := geometric_point_at (pullback (t a) (t b)) z'
    let : Field Ω := hΩ
    let : IsAlgClosed Ω := halg
    let l := w ≫ pullback.fst (t a) (t b)
    let r := w ≫ pullback.snd (t a) (t b)
    have hc : l ≫ t a = r ≫ t b := by
      simpa only [l, r, Category.assoc] using
        congrArg (fun k ↦ w ≫ k) (pullback.condition (f := t a) (g := t b))
    have hlr : l = r := by
      have h := congrArg (fun k ↦ k ≫ pullback.snd π x) hc
      simpa only [Category.assoc, ht, Category.comp_id] using h
    have he : (l ≫ s) ≫ σ a = (l ≫ s) ≫ σ b := by
      have h := congrArg (fun k ↦ k ≫ pullback.fst π x) hc
      simpa only [hlr, t, Category.assoc, pullback.lift_fst] using h
    obtain ⟨c, hc', hu⟩ := htrans Ω (l ≫ s) ((l ≫ s) ≫ σ a) (by
      simp only [Category.assoc, hσ])
    exact False.elim (hab ((hu a rfl).trans (hu b he).symm))

/-- The Artin–Schreier cover is surjective, including over the empty scheme.
Source: blueprint lemma-artin-schreier-character-sheaf, simple transitivity and existence of
geometric roots (blueprint: lem-fd-as-root-sheets-colimit).

Proof: lift each point to the spectrum of the algebraic closure of its residue
field, use existence of a root on that geometric fibre, and take the image of its
unique point. -/
theorem artinSchreierCover_surjective (p : ℕ) [Fact p.Prime]
    (X : Scheme.{u}) (hchar : (p : Γ(X, ⊤)) = 0) (f : Γ(X, ⊤)) :
    Surjective (artinSchreierCover p X f).hom := by
  obtain ⟨_, _, _, σ, _, hgeo, _⟩ := artinSchreier_cover_properties p X hchar f
  constructor
  intro z
  obtain ⟨Ω, hΩ, hclosed, x, hx⟩ := geometric_point_at X z
  let : Field Ω := hΩ
  let : IsAlgClosed Ω := hclosed
  obtain ⟨s, hs⟩ := (hgeo Ω x).1.some
  refine ⟨s default, ?_⟩
  change (s ≫ (artinSchreierCover p X f).hom) default = z
  rw [hs, hx]

end AlgebraicGeometry
