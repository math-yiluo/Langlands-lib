/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Monoidality of conjugates between right adjoints -/

@[expose] public section

set_option autoImplicit false

universe v₁ u₁ v₂ u₂

namespace CategoryTheory

/-- The right-adjoint conjugate of a monoidal transformation between strong monoidal
left adjoints is monoidal.

Source: the mate formula for monoidal adjunctions, used in latest blueprint
`prop-kernel-lisse.proof.md` to transport the algebra structure of functions
(blueprint: lem-kernel-monoidal-right-conjugate).

Proof. The conjugate is the composite of the second adjunction unit, the image of the
left-adjoint transformation, and the image of the first counit, with associators and
unitors inserted. Units and counits of strong monoidal adjunctions are monoidal, as
are whiskerings, compositions and the functor associators and unitors. -/
theorem isMonoidal_rightConjugate
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    [L₁.Monoidal] [L₂.Monoidal] [R₁.LaxMonoidal] [R₂.LaxMonoidal]
    [adj₁.IsMonoidal] [adj₂.IsMonoidal]
    (α : L₂ ⟶ L₁) [NatTrans.IsMonoidal α] :
    NatTrans.IsMonoidal (conjugateEquiv adj₁ adj₂ α) := by
  have h : conjugateEquiv adj₁ adj₂ α =
      R₁.rightUnitor.inv ≫ Functor.whiskerLeft R₁ adj₂.unit ≫
        (Functor.associator R₁ L₂ R₂).inv ≫
        Functor.whiskerRight (Functor.whiskerLeft R₁ α) R₂ ≫
        Functor.whiskerRight adj₁.counit R₂ ≫ R₂.leftUnitor.hom := by
    ext X
    simp [conjugateEquiv, mateEquiv]
  rw [h]
  infer_instance

end CategoryTheory
