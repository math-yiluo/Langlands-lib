/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Basic

/-!
# Extending morphisms into injective objects along arbitrary morphisms

In an abelian category, a morphism `δ : X ⟶ I` into an injective object factors through a
morphism `μ : X ⟶ Y` as soon as it vanishes on the kernel of `μ`: it then factors through the
image of `μ`, a subobject of `Y`, along which it extends by injectivity.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Injective

/-- In an abelian category, a morphism `δ : X ⟶ I` to an injective object which vanishes on
the kernel of `μ : X ⟶ Y` factors through `μ`. -/
theorem exists_comp_eq_of_kernel_ι_comp_eq_zero {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]
    {X Y I : 𝒜} [Injective I] (μ : X ⟶ Y) (δ : X ⟶ I) (h : kernel.ι μ ≫ δ = 0) :
    ∃ β : Y ⟶ I, μ ≫ β = δ := by
  obtain ⟨β, hβ⟩ : ∃ β, (Abelian.coimageImageComparison μ ≫ Abelian.image.ι μ) ≫ β =
      cokernel.desc _ δ h := ⟨_, Injective.comp_factorThru _ _⟩
  refine ⟨β, ?_⟩
  rw [← Abelian.coimage_image_factorisation μ, Category.assoc, hβ]
  exact cokernel.π_desc _ _ _

end CategoryTheory.Injective
