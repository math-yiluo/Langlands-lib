/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Transport of left-unit coherence through representatives -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
namespace CategoryTheory

/-- Normalized tensor and unit representative squares imply left unitality.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-left-unit-transport).
Proof: tensor the unit normalization with the representative at X. Tensorator
naturality and its normalization turn one side into the image of the ordinary
left-unit law. The other side is the proposed left-unit composite followed by
the representative. Cancel that monomorphism. -/
theorem leftUnit_on_representative
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory H]
    (Q : C ⥤ D) [Q.LaxMonoidal] (R : E ⥤ H) [R.LaxMonoidal]
    (F : C ⥤ E) [F.OplaxMonoidal] (S : D ⥤ H)
    (r : Q ⋙ S ⟶ F ⋙ R)
    (δ : ∀ X Y : D, S.obj (X ⊗ Y) ⟶ S.obj X ⊗ S.obj Y)
    (η : S.obj (𝟙_ D) ⟶ 𝟙_ H)
    (hδ : ∀ X {Y Z : D} (f : Y ⟶ Z),
      S.map (f ▷ X) ≫ δ Z X = δ Y X ≫ (S.map f ▷ S.obj X))
    (ht : ∀ X Y : C,
      δ (Q.obj X) (Q.obj Y) ≫ (r.app X ⊗ₘ r.app Y) ≫
        Functor.LaxMonoidal.μ R (F.obj X) (F.obj Y) =
      S.map (Functor.LaxMonoidal.μ Q X Y) ≫ r.app (X ⊗ Y) ≫
        R.map (Functor.OplaxMonoidal.δ F X Y))
    (hu : S.map (Functor.LaxMonoidal.ε Q) ≫ r.app (𝟙_ C) ≫
      R.map (Functor.OplaxMonoidal.η F) = η ≫ Functor.LaxMonoidal.ε R)
    (X : C) [Mono (r.app X)] :
    δ (𝟙_ D) (Q.obj X) ≫ (η ▷ S.obj (Q.obj X)) ≫ (λ_ (S.obj (Q.obj X))).hom =
      S.map (λ_ (Q.obj X)).hom := by
  apply (cancel_mono (r.app X)).1
  have h := congrArg (fun z ↦ δ (𝟙_ D) (Q.obj X) ≫
    (z ⊗ₘ r.app X) ≫ Functor.LaxMonoidal.μ R (𝟙_ E) (F.obj X) ≫
      R.map (λ_ (F.obj X)).hom) hu
  have hleft : δ (𝟙_ D) (Q.obj X) ≫
      ((S.map (Functor.LaxMonoidal.ε Q) ≫ r.app (𝟙_ C) ≫
        R.map (Functor.OplaxMonoidal.η F)) ⊗ₘ r.app X) ≫
      Functor.LaxMonoidal.μ R (𝟙_ E) (F.obj X) ≫ R.map (λ_ (F.obj X)).hom =
      S.map (λ_ (Q.obj X)).hom ≫ r.app X := by
    simp only [tensorHom_def', comp_whiskerRight, Category.assoc, Functor.comp_obj]
    rw [whisker_exchange_assoc]
    rw [← reassoc_of% (hδ (Q.obj X) (Functor.LaxMonoidal.ε Q))]
    rw [Functor.LaxMonoidal.μ_natural_left_assoc]
    rw [← tensorHom_def'_assoc, reassoc_of% (ht (𝟙_ C) X)]
    simp only [← R.map_comp]
    rw [Functor.OplaxMonoidal.left_unitality_hom]
    have hn := r.naturality (λ_ X).hom
    dsimp only [Functor.comp_map] at hn
    rw [← hn]
    simp only [Functor.LaxMonoidal.left_unitality, Functor.map_comp, Category.assoc]
  have hright : δ (𝟙_ D) (Q.obj X) ≫
      ((η ≫ Functor.LaxMonoidal.ε R) ⊗ₘ r.app X) ≫
      Functor.LaxMonoidal.μ R (𝟙_ E) (F.obj X) ≫ R.map (λ_ (F.obj X)).hom =
      (δ (𝟙_ D) (Q.obj X) ≫ (η ▷ S.obj (Q.obj X)) ≫
        (λ_ (S.obj (Q.obj X))).hom) ≫ r.app X := by
    simp only [tensorHom_def', comp_whiskerRight, Category.assoc, Functor.comp_obj]
    rw [← Functor.LaxMonoidal.left_unitality]
    rw [whisker_exchange_assoc, leftUnitor_naturality]
  exact hright.symm.trans (h.symm.trans hleft)

/-- The left-unit composite of a natural scalar tensor comparison.
Source: Stacks 07A4 (blueprint: lem-pur-scalar-left-unit-transport). -/
def scalarLeftUnitMap
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (S : C ⥤ D)
    (δ : Functor.uncurry.obj (curriedTensor C) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (curriedTensor D))
    (e : S.obj (𝟙_ C) ⟶ 𝟙_ D) : tensorLeft (𝟙_ C) ⋙ S ⟶ S where
  app X := δ.hom.app (𝟙_ C, X) ≫ (e ▷ S.obj X) ≫ (λ_ (S.obj X)).hom
  naturality {X Y} f := by
    have h := δ.hom.naturality (show (𝟙_ C, X) ⟶ (𝟙_ C, Y) from (𝟙 _, f))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map] at h
    simp only [Functor.map_id, NatTrans.id_app, Category.id_comp] at h
    change S.map (𝟙_ C ◁ f) ≫ _ = _
    simp only [Category.assoc]
    change S.map (𝟙_ C ◁ f) ≫ δ.hom.app (𝟙_ C, Y) =
      δ.hom.app (𝟙_ C, X) ≫ (S.obj (𝟙_ C) ◁ S.map f) at h
    rw [reassoc_of% h, whisker_exchange_assoc, leftUnitor_naturality]
    rfl

end CategoryTheory
