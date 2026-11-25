/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# A family isomorphic to a covering is a covering

Source: literature/stacks-project/sites.tex, Definition 00VH and Definition 00VU
(blueprint: lem-weil-pbc-site-covering-isomorphic-family)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory

/-- A family of arrows isomorphic over its target to a covering family is covering
up to a bijective reindexing, and hence is covering after reindexing.

Proof (blueprint: lem-weil-pbc-site-covering-isomorphic-family):
1. Base change the covering `g` along `φ` using
   `Precoverage.IsStableUnderBaseChange` and the chosen pullbacks supplied by
   `Precoverage.HasPullbacks`.
2. For each index, the commuting square formed by `σ a` and `φ` is a pullback:
   its universal factorization is obtained by composing with the inverses of
   these isomorphisms.
3. The chosen pullback and `(Vₐ a, σ a, f a)` are therefore uniquely
   isomorphic, with the projection to `V` identified with `f a`.
4. Each comparison isomorphism is a singleton covering by `HasIsos`; composing
   these singleton coverings with the base-changed covering uses
   `IsStableUnderComposition`.
5. The resulting indexing type is a sigma type of singleton indices, hence is
   bijective with `A`; this gives the reindexed covering. Presieves identify
   bijective reindexings, giving the final covering clause.
-/
theorem site_covering_isomorphic_family
    {C : Type u} [Category.{v} C] (J : Precoverage C)
    [Precoverage.HasIsos J] [Precoverage.IsStableUnderComposition J]
    [Precoverage.IsStableUnderBaseChange J] [Precoverage.HasPullbacks J]
    {A : Type (max u v)} {U : C} {Uₐ : A → C} (g : ∀ a, Uₐ a ⟶ U)
    (hg : Presieve.ofArrows Uₐ g ∈ J U) {V : C} (φ : V ⟶ U) [IsIso φ]
    {Vₐ : A → C} (f : ∀ a, Vₐ a ⟶ V) (σ : ∀ a, Vₐ a ⟶ Uₐ a)
    (hσ : ∀ a, IsIso (σ a))
    (compat : ∀ a, σ a ≫ g a = f a ≫ φ) :
    (∃ (A' : Type (max u v)) (β : A' ≃ A),
      Presieve.ofArrows (fun a' => Vₐ (β a')) (fun a' => f (β a')) ∈ J V) ∧
      Presieve.ofArrows Vₐ f ∈ J V := by
  have hf : Presieve.ofArrows Vₐ f ∈ J V := by
    refine Precoverage.mem_coverings_of_isPullback g hg φ f σ ?_
    intro a
    have : IsIso (σ a) := hσ a
    exact IsPullback.of_vert_isIso ⟨(compat a).symm⟩
  exact ⟨⟨A, Equiv.refl A, hf⟩, hf⟩

end CategoryTheory
