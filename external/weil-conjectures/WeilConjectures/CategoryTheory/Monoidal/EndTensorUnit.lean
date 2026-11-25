/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Endomorphisms of the monoidal unit commute

By the Eckmann–Hilton argument, the endomorphisms of the unit `𝟙_ C` of a monoidal category
commute with each other (`CategoryTheory.MonoidalCategory.tensorUnit_endo_comm`). Hence in a
preadditive monoidal category, `End (𝟙_ C)` is a commutative ring
(`CategoryTheory.MonoidalCategory.instCommRingEndTensorUnit`), and it is a field as soon as all
its nonzero elements are invertible (`CategoryTheory.MonoidalCategory.isField_end_tensorUnit`).
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- For endomorphisms `s`, `t` of the unit, `s ⊗ t` is `s ≫ t` up to the unitor
`𝟙_ C ⊗ 𝟙_ C ≅ 𝟙_ C`. -/
lemma rightUnitor_inv_comp_tensorHom_comp_rightUnitor_hom (s t : 𝟙_ C ⟶ 𝟙_ C) :
    (ρ_ (𝟙_ C)).inv ≫ (s ⊗ₘ t) ≫ (ρ_ (𝟙_ C)).hom = s ≫ t := by
  rw [tensorHom_def, Category.assoc, ← rightUnitor_inv_naturality_assoc, ← unitors_equal,
    ← unitors_inv_equal, leftUnitor_naturality, Iso.inv_hom_id_assoc]

/-- **Eckmann–Hilton**: endomorphisms of the monoidal unit commute. -/
theorem tensorUnit_endo_comm (s t : 𝟙_ C ⟶ 𝟙_ C) : s ≫ t = t ≫ s := by
  rw [← rightUnitor_inv_comp_tensorHom_comp_rightUnitor_hom, tensorHom_def', Category.assoc,
    rightUnitor_naturality, ← unitors_inv_equal, ← leftUnitor_inv_naturality_assoc,
    ← unitors_equal, Iso.inv_hom_id_assoc]

variable [Preadditive C]

/-- The endomorphism ring of the monoidal unit is commutative. -/
instance instCommRingEndTensorUnit : CommRing (End (𝟙_ C)) where
  __ := (inferInstance : Ring (End (𝟙_ C)))
  mul_comm s t := End.ext (tensorUnit_endo_comm t.asHom s.asHom)

/-- If every nonzero endomorphism of the monoidal unit is invertible and `𝟙_ C` is not a zero
object, then `End (𝟙_ C)` is a field. -/
theorem isField_end_tensorUnit (hK : ∀ t : End (𝟙_ C), t ≠ 0 → IsIso (t).asHom)
    (h₁ : (1 : End (𝟙_ C)) ≠ 0) : IsField (End (𝟙_ C)) where
  exists_pair_ne := ⟨0, 1, h₁.symm⟩
  mul_comm := mul_comm
  mul_inv_cancel {t} ht := by
    have := hK t ht
    exact ⟨.of (inv t.asHom), End.ext (IsIso.inv_hom_id t.asHom)⟩

end CategoryTheory.MonoidalCategory
