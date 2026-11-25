/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.Category

/-!
# Naturality squares for transformations between composites

The naturality of a natural transformation whose source or target is a composite of functors,
stated with the composite unfolded, so that rewriting with it does not depend on unfolding
`Functor.comp`.
-/

@[expose] public section

namespace CategoryTheory.NatTrans

/-- The naturality of a natural transformation out of a composite, stated for abstract functors
so that its instances are checked syntactically. -/
lemma app_comp_map
    {𝒜 ℬ 𝒞 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒞]
    {F₁ : 𝒜 ⥤ ℬ} {F₂ : ℬ ⥤ 𝒞} {G : 𝒜 ⥤ 𝒞} (β : F₁ ⋙ F₂ ⟶ G) {A A' : 𝒜} (f : A ⟶ A') :
    β.app A ≫ G.map f = F₂.map (F₁.map f) ≫ β.app A' :=
  (β.naturality f).symm

/-- The naturality of a natural transformation between composites, evaluated at objects, stated
for abstract functors so that its instances are checked syntactically. -/
lemma app_comp_map_map_eq
    {𝒜 ℬ ℬ' 𝒞 : Type*} [Category* 𝒜] [Category* ℬ]
    [Category* ℬ'] [Category* 𝒞] {F₁ : 𝒜 ⥤ ℬ} {F₂ : ℬ ⥤ 𝒞} {G₁ : 𝒜 ⥤ ℬ'} {G₂ : ℬ' ⥤ 𝒞}
    (β : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂) {A A' : 𝒜} (f : A ⟶ A') :
    β.app A ≫ G₂.map (G₁.map f) = F₂.map (F₁.map f) ≫ β.app A' :=
  (β.naturality f).symm

end CategoryTheory.NatTrans
