/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# Pulling back and comparing short exact sequences

For a short complex `S : X₁ ⟶ X₂ ⟶ X₃` in an abelian category and `φ : Y ⟶ X₃`, the short
complex `X₁ ⟶ X₂ ×_{X₃} Y ⟶ Y` (`CategoryTheory.ShortComplex.pullback`) is short exact when `S`
is (`CategoryTheory.ShortComplex.ShortExact.pullback`), and comes with a morphism to `S`
(`CategoryTheory.ShortComplex.pullbackHom`) which is the identity on `X₁`.

Two short exact sequences whose middle terms are identified by an isomorphism compatible with
the maps are isomorphic (`CategoryTheory.ShortComplex.ShortExact.isoOfCompEqZero`).

We also show that a product of short exact sequences is exact
(`CategoryTheory.ShortComplex.exact_mk_piMap`), that a short exact sequence in a functor category is
short exact objectwise (`CategoryTheory.ShortComplex.ShortExact.map_evaluation`), and a
five-lemma style criterion for the third component of a morphism of short complexes to be an
isomorphism (`CategoryTheory.ShortComplex.isIso_τ₃_of_exact`).
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Limits

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C) {Y : C} (φ : Y ⟶ S.X₃)

/-- The pullback `X₁ ⟶ X₂ ×_{X₃} Y ⟶ Y` of a short complex `X₁ ⟶ X₂ ⟶ X₃` along `φ : Y ⟶ X₃`. -/
noncomputable def pullback : ShortComplex C :=
  ShortComplex.mk (pullback.lift S.f 0 (by simp)) (pullback.snd S.g φ) (by simp)

/-- The morphism from the pullback of a short complex to the short complex. -/
@[simps]
noncomputable def pullbackHom : S.pullback φ ⟶ S where
  τ₁ := 𝟙 _
  τ₂ := pullback.fst _ _
  τ₃ := φ
  comm₁₂ := by simp [ShortComplex.pullback]
  comm₂₃ := pullback.condition

variable {S}

/-- The pullback of a short exact sequence is short exact. -/
lemma ShortExact.pullback (hS : S.ShortExact) : (S.pullback φ).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have : Mono (S.pullback φ).f := by
    have h : (S.pullback φ).f ≫ Limits.pullback.fst S.g φ = S.f := Limits.pullback.lift_fst _ _ _
    exact mono_of_mono_fac h
  refine { exact := ShortComplex.exact_of_f_is_kernel _ ?_
           epi_g := inferInstanceAs (Epi (Limits.pullback.snd S.g φ)) }
  refine KernelFork.IsLimit.ofι _ _ (fun {W} t ht ↦ hS.exact.lift (t ≫ Limits.pullback.fst _ _)
      (by
        have ht' : t ≫ Limits.pullback.snd S.g φ = 0 := ht
        rw [Category.assoc, Limits.pullback.condition, reassoc_of% ht', zero_comp]))
    (fun {W} t ht ↦ ?_) (fun {W} t ht m hm ↦ ?_)
  · apply Limits.pullback.hom_ext
    · simp [ShortComplex.pullback]
    · simp only [ShortComplex.pullback, Category.assoc, Limits.pullback.lift_snd, comp_zero]
      exact ht.symm
  · rw [← cancel_mono (S.pullback φ).f, hm]
    apply Limits.pullback.hom_ext
    · simp [ShortComplex.pullback]
    · simp only [ShortComplex.pullback, Category.assoc, Limits.pullback.lift_snd, comp_zero]
      exact ht

variable (S) in
/-- For `ψ : Y' ⟶ Y` and `φ : Y ⟶ X₃`, the morphism from the pullback of a short complex along
`ψ ≫ φ` to its pullback along `φ`, which is the identity on `X₁`. -/
@[simps]
noncomputable def pullbackMap {Y' : C} (ψ : Y' ⟶ Y) : S.pullback (ψ ≫ φ) ⟶ S.pullback φ where
  τ₁ := 𝟙 _
  τ₂ := Limits.pullback.lift (Limits.pullback.fst _ _) (Limits.pullback.snd _ _ ≫ ψ)
    (by rw [Limits.pullback.condition, Category.assoc])
  τ₃ := ψ
  comm₁₂ := by
    apply Limits.pullback.hom_ext <;> simp [ShortComplex.pullback]
  comm₂₃ := by simp [ShortComplex.pullback]

/-- Two short exact sequences `S` and `S'` are isomorphic via an isomorphism `e : S.X₂ ≅ S'.X₂`
of their middle terms, provided `S.f ≫ e.hom ≫ S'.g = 0` and `S'.f ≫ e.inv ≫ S.g = 0`. -/
noncomputable def ShortExact.isoOfCompEqZero {S S' : ShortComplex C} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (e : S.X₂ ≅ S'.X₂) (h₁ : S.f ≫ e.hom ≫ S'.g = 0)
    (h₂ : S'.f ≫ e.inv ≫ S.g = 0) :
    S ≅ S' :=
  have := hS.mono_f
  have := hS.epi_g
  have := hS'.mono_f
  have := hS'.epi_g
  { hom :=
      { τ₁ := hS'.exact.lift (S.f ≫ e.hom) (by rw [Category.assoc, h₁])
        τ₂ := e.hom
        τ₃ := hS.exact.desc (e.hom ≫ S'.g) (by rw [← Category.assoc] at h₁ ⊢; exact h₁)
        comm₁₂ := hS'.exact.lift_f _ _
        comm₂₃ := (hS.exact.g_desc _ _).symm }
    inv :=
      { τ₁ := hS.exact.lift (S'.f ≫ e.inv) (by rw [Category.assoc, h₂])
        τ₂ := e.inv
        τ₃ := hS'.exact.desc (e.inv ≫ S.g) (by rw [← Category.assoc] at h₂ ⊢; exact h₂)
        comm₁₂ := hS.exact.lift_f _ _
        comm₂₃ := (hS'.exact.g_desc _ _).symm }
    hom_inv_id := by
      ext
      · rw [← cancel_mono S.f]
        simp [ShortComplex.Exact.lift_f]
      · simp
      · rw [← cancel_epi S.g]
        simp [reassoc_of% (hS.exact.g_desc _ _), ShortComplex.Exact.g_desc]
    inv_hom_id := by
      ext
      · rw [← cancel_mono S'.f]
        simp [ShortComplex.Exact.lift_f]
      · simp
      · rw [← cancel_epi S'.g]
        simp [reassoc_of% (hS'.exact.g_desc _ _), ShortComplex.Exact.g_desc] }

/-- The middle component of `ShortExact.isoOfCompEqZero` is the given isomorphism. -/
@[simp]
lemma ShortExact.isoOfCompEqZero_hom_τ₂ {S S' : ShortComplex C} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (e : S.X₂ ≅ S'.X₂) (h₁ : S.f ≫ e.hom ≫ S'.g = 0)
    (h₂ : S'.f ≫ e.inv ≫ S.g = 0) :
    (hS.isoOfCompEqZero hS' e h₁ h₂).hom.τ₂ = e.hom :=
  rfl

/-- Let `φ : S₁ ⟶ S₂` be a morphism of short complexes such that `S₁.g` is an epimorphism and
`S₂` is exact with `S₂.g` an epimorphism. If `φ.τ₁` and `φ.τ₂` are isomorphisms, then so is
`φ.τ₃`:
```
S₁.X₁ ⟶ S₁.X₂ ⟶ S₁.X₃ ⟶ 0
  |≅       |≅       |φ.τ₃
  v        v        v
S₂.X₁ ⟶ S₂.X₂ ⟶ S₂.X₃ ⟶ 0
```
-/
lemma isIso_τ₃_of_exact {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) [Epi S₁.g] (h₂ : S₂.Exact)
    [Epi S₂.g] [IsIso φ.τ₁] [IsIso φ.τ₂] : IsIso φ.τ₃ := by
  refine ⟨h₂.desc (inv φ.τ₂ ≫ S₁.g) ?_, ?_, ?_⟩
  · rw [← cancel_epi φ.τ₁, Limits.comp_zero, ← Category.assoc, φ.comm₁₂, Category.assoc,
      IsIso.hom_inv_id_assoc, S₁.zero]
  · rw [← cancel_epi S₁.g, ← Category.assoc, ← φ.comm₂₃, Category.assoc, h₂.g_desc,
      IsIso.hom_inv_id_assoc, Category.comp_id]
  · rw [← cancel_epi S₂.g, ← Category.assoc, h₂.g_desc, Category.assoc, ← φ.comm₂₃,
      IsIso.inv_hom_id_assoc, Category.comp_id]

/-- A product of short exact short complexes is exact. -/
lemma exact_mk_piMap {ι : Type*} (S : ι → ShortComplex C) [HasProduct fun i ↦ (S i).X₁]
    [HasProduct fun i ↦ (S i).X₂] [HasProduct fun i ↦ (S i).X₃] (hS : ∀ i, (S i).ShortExact)
    (w : Limits.Pi.map (fun i ↦ (S i).f) ≫ Limits.Pi.map (fun i ↦ (S i).g) = 0) :
    (ShortComplex.mk _ _ w).Exact := by
  have (i : ι) : Mono (S i).f := (hS i).mono_f
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
    (fun z hz ↦ Pi.lift fun i ↦ (hS i).exact.lift (z ≫ Pi.π (fun i ↦ (S i).X₂) i) ?_)
      (fun z hz ↦ ?_) (fun z hz m hm ↦ ?_))
  · simpa using congrArg (· ≫ Pi.π (fun i ↦ (S i).X₃) i) hz
  · refine Pi.hom_ext _ _ fun i ↦ ?_
    rw [Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc, Exact.lift_f]
  · refine Pi.hom_ext _ _ fun i ↦ ?_
    rw [Pi.lift_comp_π, ← cancel_mono (S i).f, Exact.lift_f, ← hm, Category.assoc, Category.assoc,
      Pi.map_π]

/-- A short exact sequence in a functor category with values in an abelian category is short
exact objectwise. -/
lemma ShortExact.map_evaluation {J : Type*} [Category* J] {S : ShortComplex (J ⥤ C)}
    (hS : S.ShortExact) (X : J) : (S.map ((evaluation J C).obj X)).ShortExact :=
  hS.map_of_exact _

end CategoryTheory.ShortComplex
