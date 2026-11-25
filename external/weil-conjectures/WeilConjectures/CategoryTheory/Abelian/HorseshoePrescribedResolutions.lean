/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.CategoryTheory.Abelian.HorseshoePrescribedRows

/-!
# Horseshoe lemma with prescribed end resolutions

Source: Stacks Project, Derived Categories, Tag 013T, proof Step 2, specialized to objects
(blueprint: lem-sp-horseshoe-prescribed-resolutions).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

/-- Prescribed resolutions of the ends of a short exact sequence extend to a resolution
of the middle, with compatible augmentations and split short exact rows in every degree.
The rows are stated in the form used by `extMk_resolution_connecting_eq_triangle`.
Natural-number indexing represents the requirement that all three complexes vanish in
negative degrees. The isomorphisms identify the middle terms with the biproducts and the
row maps with the inclusion and projection.

Source: Stacks Project, Derived Categories, Tag 013T, proof Step 2, for objects
(blueprint: lem-sp-horseshoe-prescribed-resolutions).

Proof, Step 1: for a short exact sequence A' -> B' -> C' and embeddings u : A' -> J_A,
v : C' -> J_C into injectives, extend u through A' -> B' by injectivity
(def-sp-injective-resolutions). Together with B' -> C' -> J_C this defines an embedding
w : B' -> J_A ⊞ J_C and a commutative diagram with a split exact bottom row.
Step 2: apply the snake lemma (lem-weil-pbc-snake-lemma-abelian). Since u and v are mono,
w is mono and their cokernels form a short exact sequence, compatible with the quotient
maps and the inclusion and projection.
Step 3: start with the given augmentations. At each subsequent degree apply Steps 1 and 2
to the short exact sequence of cokernels, using the embeddings into the next prescribed
outer resolution terms supplied by exactness (def-sp-injective-resolutions). Set each
middle term to the biproduct and its differential to the quotient map followed by the
next embedding. Neither outer resolution is changed.
Step 4: the compatible quotient and embedding squares make the inclusions and projections
cochain maps and give the augmentation squares. Each differential has kernel equal to the
image of the preceding differential; in degree zero its kernel is the image of the mono
augmentation. All middle terms are injective, so this is an injective resolution
(def-sp-injective-resolutions). Each degreewise row is the split biproduct sequence. -/
theorem exists_horseshoe_prescribed_resolutions
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    (S : ShortComplex C) (hS : S.ShortExact)
    (IA : InjectiveResolution S.X₁) (IC : InjectiveResolution S.X₃) :
    ∃ (IB : InjectiveResolution S.X₂)
      (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex),
      IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ IB.ι ∧
      IB.ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι ∧
      ∃ (hαβ : α ≫ β = 0), ∀ n : ℕ,
        ((ShortComplex.mk α β hαβ).map
          (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact ∧
        ∃ e : IB.cocomplex.X n ≅ IA.cocomplex.X n ⊞ IC.cocomplex.X n,
          α.f n ≫ e.hom = biprod.inl ∧ β.f n = e.hom ≫ biprod.snd := by
  have := hS.mono_f
  let lift : S.X₂ ⟶ IA.cocomplex.X 0 := Injective.factorThru (IA.ι.f 0) S.f
  have hlift : S.f ≫ lift = IA.ι.f 0 := Injective.comp_factorThru _ _
  let w : S.X₂ ⟶ IA.cocomplex.X 0 ⊞ IC.cocomplex.X 0 :=
    biprod.lift lift (S.g ≫ IC.ι.f 0)
  have hwf : S.f ≫ w = IA.ι.f 0 ≫ biprod.inl := by
    apply biprod.hom_ext <;> simp [w, Category.assoc, hlift, S.zero_assoc]
  have hwg : w ≫ biprod.snd = S.g ≫ IC.ι.f 0 := by simp [w]
  let F : S ⟶ ShortComplex.mk
      (biprod.inl : IA.cocomplex.X 0 ⟶ IA.cocomplex.X 0 ⊞ IC.cocomplex.X 0)
      biprod.snd (by simp) :=
    { τ₁ := IA.ι.f 0
      τ₂ := w
      τ₃ := IC.ι.f 0
      comm₁₂ := hwf.symm
      comm₂₃ := hwg }
  have hw : Mono w := ShortComplex.mono_τ₂_of_exact_of_mono F hS.exact
  obtain ⟨K, ι, α, β, hα, hβ, ⟨e₀, he₀⟩, hexact₀, hαβ, hrows⟩ :=
    exists_horseshoe_prescribed_rows S hS IA IC lift hlift
  have hmono : Mono (ι.f 0) := by
    have hm : Mono (ι.f 0 ≫ e₀.hom) := by rw [he₀]; exact hw
    exact mono_of_mono (ι.f 0) e₀.hom
  have hses := HomologicalComplex.shortExact_of_degreewise_shortExact
    (ShortComplex.mk α β hαβ) hrows
  have hsplit (n : ℕ) :
      (ShortComplex.mk (α.f n) (β.f n)
        (by simpa using congrArg (fun f ↦ f.f n) hαβ)).Splitting := by
    have hr : (ShortComplex.mk (α.f n) (β.f n)
      (by simpa using congrArg (fun f ↦ f.f n) hαβ)).ShortExact := hrows n
    exact hr.splittingOfInjective
  have hinj (n : ℕ) : Injective (K.X n) := by
    let e := (hsplit n).isoBinaryBiproduct
    exact Injective.of_iso e.symm inferInstance
  let IB : InjectiveResolution S.X₂ :=
    { cocomplex := K
      injective := hinj
      ι := ι
      quasiIso := ⟨fun n ↦ by
        cases n with
        | zero =>
          rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
          · exact (ShortComplex.exact_and_mono_f_iff_of_iso
              (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
                (by simp) (by simp))).2 ⟨hexact₀, hmono⟩
          all_goals simp
        | succ n =>
          rw [quasiIsoAt_iff_exactAt]
          · exact hses.exactAt_X₂ (n + 1) (IA.cocomplex_exactAt_succ n)
              (IC.cocomplex_exactAt_succ n)
          · exact CochainComplex.exactAt_succ_single_obj _ _⟩ }
  refine ⟨IB, α, β, hα, hβ, hαβ, fun n ↦ ⟨hrows n, ?_⟩⟩
  refine ⟨(hsplit n).isoBinaryBiproduct, ?_, ?_⟩
  · apply biprod.hom_ext <;>
      simp [ShortComplex.Splitting.isoBinaryBiproduct, Category.assoc,
        (hsplit n).f_r, show α.f n ≫ β.f n = 0 from
          by simpa using congrArg (fun f ↦ f.f n) hαβ]
  · simp [ShortComplex.Splitting.isoBinaryBiproduct]

end CategoryTheory.InjectiveResolution
