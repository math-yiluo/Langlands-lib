/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-!
# Adjointification of a unit satisfying the triangle identity

`CategoryTheory.Equivalence.mk F G η ε` replaces the unit `η` by its adjointification
`CategoryTheory.Equivalence.adjointifyη η ε`, so that the triangle identity holds. If `η` and `ε`
already satisfy the triangle identity, the adjointification does not change `η`.

## Main results

- `CategoryTheory.Equivalence.adjointifyη_eq`: if `F η ≫ ε F = 𝟙`, then
  `adjointifyη η ε = η`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
  {G : D ⥤ C}

/-- If the unit `η` and the counit `ε` already satisfy the triangle identity
`F η ≫ ε F = 𝟙`, then the adjointification of `η` is `η`: both are sent by the faithful functor
`F` to the inverse of `ε F`. -/
lemma adjointifyη_eq (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)
    (h : ∀ X, F.map (η.hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 _) : adjointifyη η ε = η := by
  ext X
  apply (Equivalence.mk F G η ε).functor.map_injective
  change F.map _ = F.map _
  rw [← cancel_mono (ε.hom.app (F.obj X)), adjointify_η_ε, h]
  rfl

end CategoryTheory.Equivalence
