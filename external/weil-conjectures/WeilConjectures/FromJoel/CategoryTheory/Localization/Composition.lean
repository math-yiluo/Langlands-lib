/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Composition
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Localized equivalences from localizations

Supplement to `Mathlib.CategoryTheory.Localization.Composition`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

lemma isLocalizedEquivalence_of_isLocalization (Φ : LocalizerMorphism W₁ W₂)
    (W : MorphismProperty C₁) [Φ.functor.IsLocalization W] (hW : W ≤ W₁)
    (hW' : W₂ ≤ W₁.map Φ.functor) :
    Φ.IsLocalizedEquivalence := by
  have : (Φ.functor ⋙ W₂.Q).IsLocalization W₁ :=
    Functor.IsLocalization.comp Φ.functor W₂.Q W W₂ W₁
      (fun _ _ _ h ↦ Localization.inverts W₂.Q W₂ _ (Φ.map _ h)) hW hW'
  exact IsLocalizedEquivalence.of_isLocalization_of_isLocalization Φ W₂.Q

end LocalizerMorphism

end CategoryTheory
