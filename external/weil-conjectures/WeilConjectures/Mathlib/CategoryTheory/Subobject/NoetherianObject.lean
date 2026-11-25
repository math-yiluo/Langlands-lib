/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Filtered.Basic

/-!

# Filtered colimits with a noetherian apex

In an abelian category, if the apex of a colimit cocone over a filtered category is a noetherian
object, then one of the coprojections is an epimorphism
(`CategoryTheory.exists_epi_ι_of_isNoetherianObject`): the images of the coprojections form a
directed family of subobjects whose supremum is everything, and it has a largest member.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] {J : Type w} [Category J] [IsFiltered J]
  {F : J ⥤ C} {c : Cocone F}

/-- **A filtered colimit with a noetherian apex is attained**: some coprojection of a colimit
cocone over a filtered category with noetherian apex is an epimorphism. -/
theorem exists_epi_ι_of_isNoetherianObject (hc : IsColimit c) [IsNoetherianObject c.pt] :
    ∃ j, Epi (c.ι.app j) := by
  have hne : (Set.range fun j ↦ imageSubobject (c.ι.app j)).Nonempty :=
    ⟨_, IsFiltered.nonempty.some, rfl⟩
  obtain ⟨_, ⟨j₀, rfl⟩, hmax⟩ := (wellFounded_gt (α := Subobject c.pt)).has_min _ hne
  have hle (j : J) : imageSubobject (c.ι.app j) ≤ imageSubobject (c.ι.app j₀) := by
    have h₁ : imageSubobject (c.ι.app j) ≤ imageSubobject (c.ι.app (IsFiltered.max j j₀)) := by
      rw [← c.w (IsFiltered.leftToMax j j₀)]
      exact imageSubobject_comp_le _ _
    have h₂ : imageSubobject (c.ι.app j₀) ≤ imageSubobject (c.ι.app (IsFiltered.max j j₀)) := by
      rw [← c.w (IsFiltered.rightToMax j j₀)]
      exact imageSubobject_comp_le _ _
    exact h₁.trans (eq_of_le_of_not_lt h₂ (hmax _ ⟨_, rfl⟩)).symm.le
  have harrow : (imageSubobject (c.ι.app j₀)).arrow ≫ cokernel.π (c.ι.app j₀) = 0 := by
    rw [← cancel_epi (factorThruImageSubobject (c.ι.app j₀)), comp_zero,
      imageSubobject_arrow_comp_assoc, cokernel.condition]
  refine ⟨j₀, Abelian.epi_of_cokernel_π_eq_zero _ (hc.hom_ext fun j ↦ ?_)⟩
  rw [comp_zero, ← imageSubobject_arrow_comp (c.ι.app j), ← Subobject.ofLE_arrow (hle j),
    Category.assoc, Category.assoc, harrow, comp_zero, comp_zero]

end CategoryTheory
