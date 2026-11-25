/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Basic-open refinement of an open-immersion cover of an affine scheme

Given an affine scheme `X` covered by a family of open immersions `f i : Y i ⟶ X`,
this file produces a pointwise refinement by basic opens of `X`: for every `x : X`
there is an index `i x` and a global section `g x : Γ(X, ⊤)` such that
`x ∈ D(g x)` and `D(g x)` factors through `f (i x)`.

The variant `exists_basicOpen_lift_of_isAffine_cover` additionally packages the
inclusions `D(g x) ⟶ Y (i x)` as morphisms of schemes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Pointwise basic-open refinement of an open-immersion cover `f i : Y i ⟶ X` of an
affine scheme `X`: for each `x : X` there are an index `i x` and a global section
`g x : Γ(X, ⊤)` with `x ∈ D(g x)` and `D(g x) ≤ (f (i x)).opensRange`. -/
lemma exists_basicOpen_refinement_of_isAffine_cover
    {X : Scheme.{u}} [IsAffine X] {ι : Type*} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⋃ i, Set.range (f i).base = Set.univ) :
    ∃ (i : X → ι) (g : X → Γ(X, ⊤)),
      (∀ x : X, x ∈ X.basicOpen (g x)) ∧
      (∀ x : X, X.basicOpen (g x) ≤ (f (i x)).opensRange) := by
  choose i hi using fun x : X ↦ show ∃ j, x ∈ (f j).opensRange by
    have hx : x ∈ ⋃ j, Set.range (f j).base := hcov ▸ Set.mem_univ _
    obtain ⟨_, ⟨j, rfl⟩, hxj⟩ := hx
    exact ⟨j, hxj⟩
  choose g hle hg using fun x : X ↦
    (isAffineOpen_top X).exists_basicOpen_le (V := (f (i x)).opensRange) ⟨x, hi x⟩ trivial
  exact ⟨i, g, hg, hle⟩

/-- Variant of `exists_basicOpen_refinement_of_isAffine_cover` providing lifts
`e x : D(g x) ⟶ Y (i x)` with `e x ≫ f (i x) = (D(g x)).ι`. -/
lemma exists_basicOpen_lift_of_isAffine_cover
    {X : Scheme.{u}} [IsAffine X] {ι : Type*} {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⋃ i, Set.range (f i).base = Set.univ) :
    ∃ (i : X → ι) (g : X → Γ(X, ⊤))
      (e : ∀ x, (X.basicOpen (g x) : Scheme) ⟶ Y (i x)),
      (∀ x : X, x ∈ X.basicOpen (g x)) ∧
      (∀ x : X, e x ≫ f (i x) = (X.basicOpen (g x)).ι) := by
  obtain ⟨i, g, hmem, hle⟩ :=
    exists_basicOpen_refinement_of_isAffine_cover f hcov
  refine ⟨i, g, fun x ↦ IsOpenImmersion.lift (f (i x)) (X.basicOpen (g x)).ι ?_, hmem,
    fun x ↦ IsOpenImmersion.lift_fac (f (i x)) (X.basicOpen (g x)).ι _⟩
  rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
  exact_mod_cast hle x

end AlgebraicGeometry
