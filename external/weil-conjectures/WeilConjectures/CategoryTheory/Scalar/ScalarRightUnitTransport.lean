/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Transport of right-unit coherence through representatives -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
namespace CategoryTheory

/-- Normalized tensor and unit representative squares imply right unitality.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-right-unit-transport).
Proof: tensor the unit normalization with the representative at X. Tensorator
naturality and its normalization turn one side into the image of the ordinary
right-unit law. The other side is the proposed right-unit composite followed by
the representative. Cancel that monomorphism. -/
theorem rightUnit_on_representative
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
    (Q : C ⥤ D) [Q.LaxMonoidal] (R : E ⥤ H) [R.LaxMonoidal]
    (F : C ⥤ E) [F.OplaxMonoidal] (S : D ⥤ H)
    (r : Q ⋙ S ⟶ F ⋙ R)
    (δ : ∀ X Y : D, S.obj (X ⊗ Y) ⟶ S.obj X ⊗ S.obj Y)
    (η : S.obj (𝟙_ D) ⟶ 𝟙_ H)
    (hδ : ∀ X {Y Z : D} (f : Y ⟶ Z),
      S.map (X ◁ f) ≫ δ X Z = δ X Y ≫ (S.obj X ◁ S.map f))
    (ht : ∀ X Y : C,
      δ (Q.obj X) (Q.obj Y) ≫ (r.app X ⊗ₘ r.app Y) ≫
        Functor.LaxMonoidal.μ R (F.obj X) (F.obj Y) =
      S.map (Functor.LaxMonoidal.μ Q X Y) ≫ r.app (X ⊗ Y) ≫
        R.map (Functor.OplaxMonoidal.δ F X Y))
    (hu : S.map (Functor.LaxMonoidal.ε Q) ≫ r.app (𝟙_ C) ≫
      R.map (Functor.OplaxMonoidal.η F) = η ≫ Functor.LaxMonoidal.ε R)
    (X : C) [Mono (r.app X)] :
    δ (Q.obj X) (𝟙_ D) ≫ (S.obj (Q.obj X) ◁ η) ≫ (ρ_ (S.obj (Q.obj X))).hom =
      S.map (ρ_ (Q.obj X)).hom := by
  apply (cancel_mono (r.app X)).1
  have h := congrArg (fun z ↦ δ (Q.obj X) (𝟙_ D) ≫
    (r.app X ⊗ₘ z) ≫ Functor.LaxMonoidal.μ R (F.obj X) (𝟙_ E) ≫
      R.map (ρ_ (F.obj X)).hom) hu
  have hleft : δ (Q.obj X) (𝟙_ D) ≫
      (r.app X ⊗ₘ (S.map (Functor.LaxMonoidal.ε Q) ≫ r.app (𝟙_ C) ≫
        R.map (Functor.OplaxMonoidal.η F))) ≫
      Functor.LaxMonoidal.μ R (F.obj X) (𝟙_ E) ≫ R.map (ρ_ (F.obj X)).hom =
      S.map (ρ_ (Q.obj X)).hom ≫ r.app X := by
    simp only [tensorHom_def, whiskerLeft_comp, Category.assoc, Functor.comp_obj]
    rw [← whisker_exchange_assoc]
    rw [← reassoc_of% (hδ (Q.obj X) (Functor.LaxMonoidal.ε Q))]
    rw [Functor.LaxMonoidal.μ_natural_right_assoc]
    rw [← tensorHom_def_assoc, reassoc_of% (ht X (𝟙_ C))]
    simp only [← R.map_comp]
    rw [Functor.OplaxMonoidal.right_unitality_hom]
    have hn := r.naturality (ρ_ X).hom
    dsimp only [Functor.comp_map] at hn
    rw [← hn]
    simp only [Functor.LaxMonoidal.right_unitality, Functor.map_comp, Category.assoc]
  have hright : δ (Q.obj X) (𝟙_ D) ≫
      (r.app X ⊗ₘ (η ≫ Functor.LaxMonoidal.ε R)) ≫
      Functor.LaxMonoidal.μ R (F.obj X) (𝟙_ E) ≫ R.map (ρ_ (F.obj X)).hom =
      (δ (Q.obj X) (𝟙_ D) ≫ (S.obj (Q.obj X) ◁ η) ≫
        (ρ_ (S.obj (Q.obj X))).hom) ≫ r.app X := by
    simp only [tensorHom_def, whiskerLeft_comp, Category.assoc, Functor.comp_obj]
    rw [← Functor.LaxMonoidal.right_unitality]
    rw [← whisker_exchange_assoc, rightUnitor_naturality]
  exact hright.symm.trans (h.symm.trans hleft)

/-- The right-unit composite of a natural scalar tensor comparison.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-right-unit-transport). -/
def scalarRightUnitMap
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (S : C ⥤ D)
    (δ : Functor.uncurry.obj (curriedTensor C) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (curriedTensor D))
    (e : S.obj (𝟙_ C) ⟶ 𝟙_ D) : tensorRight (𝟙_ C) ⋙ S ⟶ S where
  app X := δ.hom.app (X, 𝟙_ C) ≫ (S.obj X ◁ e) ≫ (ρ_ (S.obj X)).hom
  naturality {X Y} f := by
    have h := δ.hom.naturality (show (X, 𝟙_ C) ⟶ (Y, 𝟙_ C) from (f, 𝟙 _))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map] at h
    simp only [Functor.map_id, Category.comp_id] at h
    change S.map (f ▷ 𝟙_ C) ≫ _ = _
    simp only [Category.assoc]
    change S.map (f ▷ 𝟙_ C) ≫ δ.hom.app (Y, 𝟙_ C) =
      δ.hom.app (X, 𝟙_ C) ≫ (S.map f ▷ S.obj (𝟙_ C)) at h
    rw [reassoc_of% h, ← whisker_exchange_assoc, rightUnitor_naturality]

end CategoryTheory
