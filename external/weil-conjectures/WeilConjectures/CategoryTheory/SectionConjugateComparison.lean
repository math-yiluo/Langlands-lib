/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.SectionProjectionUnit
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Naturality of a conjugate section comparison -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory.Adjunction
/-- Direct-image coordinate interchange respects the units of a common section. -/
theorem conjugate_section_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {R : D ⥤ C} (a : F ⊣ R)
    {G₁ G₂ : D ⥤ E} {P₁ P₂ : E ⥤ D} (b₁ : G₁ ⊣ P₁) (b₂ : G₂ ⊣ P₂)
    {H : E ⥤ D} {S : D ⥤ E} (e : H ⊣ S)
    (l₁ : G₁ ⋙ H ≅ 𝟭 D) (l₂ : G₂ ⋙ H ≅ 𝟭 D)
    (c : F ⋙ G₁ ⟶ F ⋙ G₂)
    (hc : Functor.whiskerRight c H ≫ Functor.whiskerLeft F l₂.hom =
      Functor.whiskerLeft F l₁.hom) :
    Functor.whiskerRight (conjugateIsoEquiv Adjunction.id (b₂.comp e) l₂).hom R ≫
        Functor.whiskerLeft S (conjugateEquiv (a.comp b₂) (a.comp b₁) c) =
      Functor.whiskerRight (conjugateIsoEquiv Adjunction.id (b₁.comp e) l₁).hom R := by
  have ha : a.comp Adjunction.id = a := by
    apply Adjunction.ext
    ext M
    simp [Adjunction.comp_unit_app]
  have haa₁ : a.comp (b₁.comp e) = (a.comp b₁).comp e := by
    apply Adjunction.ext
    ext M
    simp [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  have haa₂ : a.comp (b₂.comp e) = (a.comp b₂).comp e := by
    apply Adjunction.ext
    ext M
    simp [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  have h₁ := conjugateEquiv_whiskerLeft Adjunction.id (b₁.comp e) a l₁.hom
  have h₂ := conjugateEquiv_whiskerLeft Adjunction.id (b₂.comp e) a l₂.hom
  rw [ha, haa₁] at h₁
  rw [ha, haa₂] at h₂
  change Functor.whiskerRight (conjugateEquiv Adjunction.id (b₂.comp e) l₂.hom) R ≫
      Functor.whiskerLeft S (conjugateEquiv (a.comp b₂) (a.comp b₁) c) =
    Functor.whiskerRight (conjugateEquiv Adjunction.id (b₁.comp e) l₁.hom) R
  rw [← h₂, ← h₁, ← conjugateEquiv_whiskerRight (a.comp b₂) (a.comp b₁) e c]
  have ht := conjugateEquiv_comp a ((a.comp b₂).comp e) ((a.comp b₁).comp e)
    (Functor.whiskerLeft F l₂.hom) (Functor.whiskerRight c H)
  exact ht.trans (congrArg (conjugateEquiv a ((a.comp b₁).comp e)) hc)
end CategoryTheory.Adjunction
