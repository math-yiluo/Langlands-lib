/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Localization formula for a square of exact functors

Source: the universal property of localization and the canonical exact-functor
composition comparisons (Stacks Project, Tags 05S7 and 014F).
(auxiliary; not a blueprint node).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  [Abelian C] [Abelian D] [Abelian E] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory F]
  (R : C ⥤ D) (G : D ⥤ F) (L : C ⥤ E) (S : E ⥤ F)
  [R.Additive] [G.Additive] [L.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- The bounded-below derived square associated to an exact ordinary square.
(auxiliary; not a blueprint node). -/
noncomputable def mapDerivedCategoryPlusSquareIso (e : R ⋙ G ≅ L ⋙ S) :
    R.mapDerivedCategoryPlus ⋙ G.mapDerivedCategoryPlus ≅
      L.mapDerivedCategoryPlus ⋙ S.mapDerivedCategoryPlus := by
  letI : PreservesFiniteLimits (R ⋙ G) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (R ⋙ G) := comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits (L ⋙ S) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits (L ⋙ S) := comp_preservesFiniteColimits _ _
  exact (mapDerivedCategoryPlusCompIso R G).symm ≪≫
    mapDerivedCategoryPlusNatIso e ≪≫ mapDerivedCategoryPlusCompIso L S

section Composition

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₀₂ : C₀ ⥤ C₂)
  (G₀₁ : D₀ ⥤ D₁) (G₁₂ : D₁ ⥤ D₂) (G₀₂ : D₀ ⥤ D₂)
  (U₀ : C₀ ⥤ D₀) (U₁ : C₁ ⥤ D₁) (U₂ : C₂ ⥤ D₂)
  [F₀₁.Additive] [F₁₂.Additive] [F₀₂.Additive]
  [G₀₁.Additive] [G₁₂.Additive] [G₀₂.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  [PreservesFiniteLimits F₀₁] [PreservesFiniteColimits F₀₁]
  [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₀₂] [PreservesFiniteColimits F₀₂]
  [PreservesFiniteLimits G₀₁] [PreservesFiniteColimits G₀₁]
  [PreservesFiniteLimits G₁₂] [PreservesFiniteColimits G₁₂]
  [PreservesFiniteLimits G₀₂] [PreservesFiniteColimits G₀₂]
  [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits (F₀₁ ⋙ F₁₂)] [PreservesFiniteColimits (F₀₁ ⋙ F₁₂)]
  [PreservesFiniteLimits (G₀₁ ⋙ G₁₂)] [PreservesFiniteColimits (G₀₁ ⋙ G₁₂)]

end Composition

end CategoryTheory.Functor
