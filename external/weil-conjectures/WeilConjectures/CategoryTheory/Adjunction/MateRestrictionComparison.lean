/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Inverse mates under a change of left adjoints

Whether an inverse mate is invertible does not depend on the choice of the left adjoints
(`isIso_mateEquiv_symm_of_isIso`).
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

section ChangeOfAdjunction

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]

/-- Whether an inverse mate is invertible does not depend on the choice of left adjoints. -/
theorem isIso_mateEquiv_symm_of_isIso {G : A ⥤ C} {H : B ⥤ D} {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A}
    {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : L₁' ⊣ R₁)
    (b₂ : L₂' ⊣ R₂) (β : TwoSquare R₁ H G R₂) [IsIso ((mateEquiv b₁ b₂).symm β)] :
    IsIso ((mateEquiv a₁ a₂).symm β) := by
  let e₁ : L₁' ≅ L₁ := (conjugateIsoEquiv a₁ b₁).symm (Iso.refl R₁)
  let e₂ : L₂' ≅ L₂ := (conjugateIsoEquiv a₂ b₂).symm (Iso.refl R₂)
  have h₁ : conjugateEquiv a₁ b₁ e₁.hom = 𝟙 R₁ :=
    (conjugateEquiv a₁ b₁).apply_symm_apply (𝟙 R₁)
  have h₂ : conjugateEquiv a₂ b₂ e₂.hom = 𝟙 R₂ :=
    (conjugateEquiv a₂ b₂).apply_symm_apply (𝟙 R₂)
  let w := (mateEquiv a₁ a₂).symm β
  let w' := (mateEquiv b₁ b₂).symm β
  have h : w'.whiskerLeft e₁.hom = w.whiskerRight e₂.hom := by
    apply (mateEquiv a₁ b₂).injective
    rw [conjugateEquiv_mateEquiv_vcomp a₁ b₁ b₂ e₁.hom w',
      mateEquiv_conjugateEquiv_vcomp a₁ a₂ b₂ w e₂.hom]
    simp only [w, w', Equiv.apply_symm_apply, h₁, h₂]
    ext X
    simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom]
  have (X : A) : IsIso (w.app X) := by
    have hc := congrArg (fun t ↦ t.app X) h
    change w'.app X ≫ H.map (e₁.hom.app X) = e₂.hom.app (G.obj X) ≫ w.app X at hc
    have : IsIso (w'.app X) := inferInstance
    have : IsIso (e₂.hom.app (G.obj X) ≫ w.app X) := by
      rw [← hc]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ this inferInstance
    exact IsIso.of_isIso_comp_left (e₂.hom.app (G.obj X)) (w.app X)
  exact NatIso.isIso_of_isIso_app _

end ChangeOfAdjunction

end CategoryTheory
