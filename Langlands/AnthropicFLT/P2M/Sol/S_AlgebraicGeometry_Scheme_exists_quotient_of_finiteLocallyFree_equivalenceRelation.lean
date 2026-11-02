/-
Ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped and its commands are replaced
by standard Lean commands; the two FLT affine-case results it uses are replaced by their
published Library versions (`existsAffineQuotient` and the finite-set invariant affine open
theorem), with the proof of `exists_invariant_affine_cover` adapted to the finite-set form.
The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationAffineQuotientProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Q1SCH

theorem exists_invariant_affine_cover
    {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ r : R, s r = x → t r ∈ U) :
    ∃ W : X → X.Opens, (∀ x, IsAffineOpen (W x)) ∧ (∀ x, x ∈ W x) ∧ (∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x) := by
  choose U hU hxU using haff
  choose W hW hxW _ hinv using fun x =>
    AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
      s t hequiv (Set.finite_singleton x) (hU x)
      (fun y hy => (Set.mem_singleton_iff.mp hy) ▸ hxU x)
  exact ⟨W, hW, fun x => hxW x (Set.mem_singleton x), hinv⟩

section restrict

variable {X R : Scheme.{u}} (s t : R ⟶ X) (W : X.Opens) (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W)

noncomputable def sW : (s ⁻¹ᵁ W).toScheme ⟶ W.toScheme := s ∣_ W

noncomputable def tW : (s ⁻¹ᵁ W).toScheme ⟶ W.toScheme := (R.isoOfEq hinv).hom ≫ (t ∣_ W)

theorem sW_ι : sW s W ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ s := by simp [sW]

theorem tW_ι : tW s t W hinv ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ t := by simp [tW]

theorem isPullback_sW : IsPullback (s ⁻¹ᵁ W).ι (sW s W) s W.ι :=
  (isPullback_morphismRestrict s W).flip

theorem isPullback_tW : IsPullback (s ⁻¹ᵁ W).ι (tW s t W hinv) t W.ι := by
  refine (isPullback_morphismRestrict t W).flip.of_iso (R.isoOfEq hinv).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp
  · simp [tW]

scoped instance [IsFinite s] : IsFinite (sW s W) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_sW s W) inferInstance
scoped instance [Flat s] : Flat (sW s W) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_sW s W) inferInstance
scoped instance [LocallyOfFinitePresentation s] : LocallyOfFinitePresentation (sW s W) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_sW s W)
    inferInstance
theorem tW_finite [IsFinite t] : IsFinite (tW s t W hinv) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_tW s t W hinv) inferInstance
theorem tW_flat [Flat t] : Flat (tW s t W hinv) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_tW s t W hinv) inferInstance
theorem tW_lfp [LocallyOfFinitePresentation t] : LocallyOfFinitePresentation (tW s t W hinv) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_tW s t W hinv)
    inferInstance

theorem mono_restrict
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    {T : Scheme.{u}} (a b : T ⟶ (s ⁻¹ᵁ W).toScheme) (h₁ : a ≫ sW s W = b ≫ sW s W)
    (h₂ : a ≫ tW s t W hinv = b ≫ tW s t W hinv) : a = b := by
  rw [← cancel_mono (s ⁻¹ᵁ W).ι]
  apply hmono
  · rw [Category.assoc, Category.assoc, ← sW_ι, reassoc_of% h₁]
  · rw [Category.assoc, Category.assoc, ← tW_ι s t W hinv, reassoc_of% h₂]

theorem rel_restrict_iff {T : Scheme.{u}} (x y : T ⟶ W.toScheme) :
    (∃ φ : T ⟶ (s ⁻¹ᵁ W).toScheme, φ ≫ sW s W = x ∧ φ ≫ tW s t W hinv = y) ↔
      ∃ ψ : T ⟶ R, ψ ≫ s = x ≫ W.ι ∧ ψ ≫ t = y ≫ W.ι := by
  constructor
  · rintro ⟨φ, rfl, rfl⟩
    exact ⟨φ ≫ (s ⁻¹ᵁ W).ι, by rw [Category.assoc, Category.assoc, sW_ι],
      by rw [Category.assoc, Category.assoc, tW_ι]⟩
  · rintro ⟨ψ, h₁, h₂⟩
    have hrange : Set.range ψ.base ⊆ Set.range (s ⁻¹ᵁ W).ι.base := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      change s (ψ p) ∈ W
      rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply]
      exact (x p).2
    refine ⟨IsOpenImmersion.lift (s ⁻¹ᵁ W).ι ψ hrange, ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, sW_ι, ← Category.assoc, IsOpenImmersion.lift_fac, h₁]
    · rw [← cancel_mono W.ι, Category.assoc, tW_ι, ← Category.assoc, IsOpenImmersion.lift_fac, h₂]

theorem equivalence_restrict
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ W.toScheme =>
      ∃ φ : T ⟶ (s ⁻¹ᵁ W).toScheme, φ ≫ sW s W = x ∧ φ ≫ tW s t W hinv = y := by
  have E := hequiv T
  exact
    { refl := fun x => (rel_restrict_iff s t W hinv x x).2 (E.refl _)
      symm := fun h => (rel_restrict_iff s t W hinv _ _).2 (E.symm ((rel_restrict_iff s t W hinv _ _).1 h))
      trans := fun h h' => (rel_restrict_iff s t W hinv _ _).2
        (E.trans ((rel_restrict_iff s t W hinv _ _).1 h) ((rel_restrict_iff s t W hinv _ _).1 h')) }

end restrict

theorem main {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ r : R, s r = x → t r ∈ U) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  obtain ⟨W, hW, hxW, hinv⟩ := exists_invariant_affine_cover s t hequiv haff

  have loc : ∀ x : X, ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (p : (W x).toScheme ⟶ Y)
      (w : sW s (W x) ≫ p = tW s t (W x) (hinv x) ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (sW s (W x)) (tW s t (W x) (hinv x)) p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
    fun x => by
      haveI : IsAffine (W x).toScheme := hW x
      haveI := tW_finite s t (W x) (hinv x)
      haveI := tW_flat s t (W x) (hinv x)
      haveI := tW_lfp s t (W x) (hinv x)
      exact Langlands.AlgebraicGeometry.FiniteLocallyFreeQuotient.existsAffineQuotient (sW s (W x)) (tW s t (W x) (hinv x))
        (fun a b h₁ h₂ => mono_restrict s t (W x) (hinv x) hmono a b h₁ h₂)
        (equivalence_restrict s t (W x) (hinv x) hequiv)

  refine AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict s t W hxW hinv fun x => ?_
  obtain ⟨Y, _, p, w, h₁, h₂, h₃, h₄, h₅, -⟩ := loc x
  exact ⟨Y, p, w, h₁, h₂, h₃, h₄, h₅⟩

end Q1SCH
open scoped _root_.P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.Q1SCH

theorem solution
    {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ r : R, s r = x → t r ∈ U) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
  Q1SCH.main s t hmono hequiv haff
