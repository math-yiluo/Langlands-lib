/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.FgSeparableSmooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.FieldTheory.SeparablyGeneratedSeparable
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Separable extensions as colimits of smooth subalgebras

Source: Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV
(blueprint: corollary-open-direct-image-over-field--2).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FieldTheory

/-- The inclusion diagram of finitely generated smooth subalgebras of a field extension.
Source: Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV
(blueprint: corollary-open-direct-image-over-field--2). -/
def smoothSubalgebraDiagram (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] :
    {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG} ⥤ CommRingCat :=
  { obj := fun A => CommRingCat.of A.1
    map := fun {A B} f =>
      CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom
    map_id := by intros; ext; rfl
    map_comp := by intros; ext; rfl }

/-- The cocone from smooth subalgebras to their ambient field, with inclusion maps.
Source: Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV
(blueprint: corollary-open-direct-image-over-field--2). -/
def smoothSubalgebraCocone (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] : Cocone (smoothSubalgebraDiagram K L) :=
  { pt := CommRingCat.of L
    ι :=
      { app := fun A => CommRingCat.ofHom A.1.val.toRingHom
        naturality := by intros; ext; rfl } }

private theorem finite_subset_of_directed_cover
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {ι : Type v} [Nonempty ι] {A : ι → Subalgebra K L}
    (hdir : Directed (· ≤ ·) A) (hcover : ∀ x : L, ∃ i, x ∈ A i)
    (s : Finset L) : ∃ i, ∀ x ∈ s, x ∈ A i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨j, hj⟩ := hcover x
    obtain ⟨k, hik, hjk⟩ := hdir i j
    refine ⟨k, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hjk hj
    · exact hik (hi y hy)

/-- For any separable field extension `L/K`, the full collection of finitely generated smooth
`K`-subalgebras of `L` is nonempty and directed under inclusion, and its union is `L`.
Its canonical cocone of inclusions is a colimit, and its image under `Spec` is a limit cone of
affine smooth `K`-schemes with affine transition maps.

Source: Stacks Project, Algebra, Lemma 10.158.11, Tag 07BV
(blueprint: corollary-open-direct-image-over-field--2). For each finitely generated subextension of
`L/K`, apply `fg_separable_extension_is_filtered_colimit_smooth`. Every finite subset of `L`
lies in one of the resulting smooth subalgebras; applying this to generators of two such
subalgebras proves directedness. The union is the ring colimit. The `Spec` functor sends its
opposite cone to a limit cone, and maps between affine schemes are affine. -/
theorem separable_extension_is_filtered_colimit_smooth
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (hsep : Algebra.IsSeparableExtension K L) :
    Nonempty {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG} ∧
      Directed (· ≤ ·)
        (fun A : {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG} => A.1) ∧
      (∀ x : L, ∃ A : {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG}, x ∈ A.1) ∧
      Nonempty (IsColimit (smoothSubalgebraCocone K L)) ∧
      Nonempty (IsLimit (Scheme.Spec.mapCone (smoothSubalgebraCocone K L).op)) ∧
      (∀ A : {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG},
        Algebra.Smooth K A.1) ∧
      (∀ (A B : {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG}) (f : B ⟶ A),
        IsAffineHom
        (Spec.map (CommRingCat.ofHom
          (Subalgebra.inclusion (leOfHom f)).toRingHom))) := by
  classical
  let S := {A : Subalgebra K L // Algebra.Smooth K A ∧ A.FG}
  have finite_cover (s : Finset L) : ∃ A : S, ∀ x ∈ s, x ∈ A.1 := by
    let F := IntermediateField.adjoin K (s : Set L)
    have hfg : F.FG := IntermediateField.fg_adjoin_finset s
    let : Algebra.EssFiniteType K F := IntermediateField.essFiniteType_iff.mpr hfg
    have hsepF := Algebra.isSeparableExtension_of_isSeparablyGenerated K F (hsep F hfg)
    obtain ⟨ι, A, hne, hsmooth, hFG, hdir, hcover⟩ :=
      fg_separable_extension_is_filtered_colimit_smooth hsepF
    let := hne
    let t : Finset F := s.attach.image (fun x ↦
      ⟨x.1, IntermediateField.subset_adjoin K (s : Set L) x.2⟩)
    obtain ⟨i, hi⟩ := finite_subset_of_directed_cover hdir hcover t
    let B := (A i).map F.val
    have hB : Algebra.Smooth K B := by
      let := hsmooth i
      exact Algebra.Smooth.of_equiv
        (Subalgebra.equivMapOfInjective (A i) F.val F.val.injective)
    refine ⟨⟨B, hB, (hFG i).map F.val⟩, ?_⟩
    intro x hx
    have ht : (⟨x, IntermediateField.subset_adjoin K (s : Set L) hx⟩ : F) ∈ t := by
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
    exact ⟨_, hi _ ht, rfl⟩
  have hne : Nonempty S := by
    obtain ⟨A, _⟩ := finite_cover ∅
    exact ⟨A⟩
  have hdir : Directed (· ≤ ·) (fun A : S ↦ A.1) := by
    intro A B
    obtain ⟨s, hs⟩ := A.2.2
    obtain ⟨t, ht⟩ := B.2.2
    obtain ⟨C, hC⟩ := finite_cover (s ∪ t)
    refine ⟨C, ?_, ?_⟩
    · change A.1 ≤ C.1
      rw [← hs]
      exact Algebra.adjoin_le fun x hx ↦ hC x (Finset.mem_union.mpr (Or.inl hx))
    · change B.1 ≤ C.1
      rw [← ht]
      exact Algebra.adjoin_le fun x hx ↦ hC x (Finset.mem_union.mpr (Or.inr hx))
  have hcover : ∀ x : L, ∃ A : S, x ∈ A.1 := by
    intro x
    obtain ⟨A, hA⟩ := finite_cover {x}
    exact ⟨A, hA x (Finset.mem_singleton_self x)⟩
  let := hne
  let : IsDirectedOrder S := ⟨hdir⟩
  have hc : IsColimit (smoothSubalgebraCocone K L) := by
    let : ReflectsColimitsOfShape S (forget CommRingCat) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    apply isColimitOfReflects (forget CommRingCat)
    apply Types.FilteredColimit.isColimitOf'
    · intro x
      obtain ⟨A, hx⟩ := hcover x
      exact ⟨A, ⟨x, hx⟩, rfl⟩
    · intro A x y hxy
      refine ⟨A, 𝟙 A, ?_⟩
      exact Subtype.ext hxy
  refine ⟨hne, hdir, hcover, ⟨hc⟩, ?_, fun A ↦ A.2.1, ?_⟩
  · exact ⟨isLimitOfPreserves Scheme.Spec hc.op⟩
  · intro A B f
    infer_instance

end FieldTheory
