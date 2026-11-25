/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CechPullbackTensorCoherence
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! # Steps of the augmented Cech pullback induction.
Source: Stacks Project, algebraization.tex, Tags 0996 and 099E; sites-modules.tex, Tag 03EL.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory
section UnitAction
universe w z
variable {A : Type w} [Category A] [MonoidalCategory A]
  {B : Type z} [Category B] [MonoidalCategory B]

private def unitAction (q : 𝟙_ B ≅ 𝟙_ B) (X : B) : X ≅ X :=
  (λ_ X).symm ≪≫ tensorIso q (Iso.refl X) ≪≫ (λ_ X)

private theorem unitAction_naturality (q : 𝟙_ B ≅ 𝟙_ B)
    {X Y : B} (f : X ⟶ Y) :
    f ≫ (unitAction q Y).hom = (unitAction q X).hom ≫ f := by
  change f ≫ (λ_ Y).inv ≫ (q.hom ⊗ₘ 𝟙 Y) ≫ (λ_ Y).hom =
    ((λ_ X).inv ≫ (q.hom ⊗ₘ 𝟙 X) ≫ (λ_ X).hom) ≫ f
  simp only [tensorHom_id, Category.assoc]
  rw [← Category.assoc f, leftUnitor_inv_naturality]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc]
  rw [leftUnitor_naturality]

private theorem unitAction_unit (q : 𝟙_ B ≅ 𝟙_ B) :
    (unitAction q (𝟙_ B)).hom = q.hom := by
  change (λ_ (𝟙_ B)).inv ≫ (q.hom ⊗ₘ 𝟙 (𝟙_ B)) ≫ (λ_ (𝟙_ B)).hom = q.hom
  rw [tensorHom_id, unitors_equal, rightUnitor_naturality]
  rw [← unitors_equal, Iso.inv_hom_id_assoc]

private theorem normalizeTensor (G : A ⥤ B)
    (e : G.obj (𝟙_ A) ≅ 𝟙_ B)
    (t : ∀ X Y, G.obj (X ⊗ Y) ≅ G.obj X ⊗ G.obj Y)
    (ht : ∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
      G.map (f ⊗ₘ g) ≫ (t X' Y').hom =
        (t X Y).hom ≫ (G.map f ⊗ₘ G.map g)) :
    ∃ t' : ∀ X Y, G.obj (X ⊗ Y) ≅ G.obj X ⊗ G.obj Y,
      (∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
        G.map (f ⊗ₘ g) ≫ (t' X' Y').hom =
          (t' X Y).hom ≫ (G.map f ⊗ₘ G.map g)) ∧
      ((t' (𝟙_ A) (𝟙_ A)).hom ≫ (e.hom ⊗ₘ e.hom) ≫ (λ_ (𝟙_ B)).hom =
        G.map (λ_ (𝟙_ A)).hom ≫ e.hom) := by
  let d : 𝟙_ B ≅ 𝟙_ B := e.symm ≪≫ G.mapIso (λ_ (𝟙_ A)).symm ≪≫
    t (𝟙_ A) (𝟙_ A) ≪≫ tensorIso e e ≪≫ (λ_ (𝟙_ B))
  refine ⟨fun X Y ↦ t X Y ≪≫ unitAction d.symm _, ?_, ?_⟩
  · intro X X' Y Y' f g
    dsimp only [Iso.trans_hom]
    rw [← Category.assoc, ht]
    simp only [Category.assoc]
    rw [unitAction_naturality]
  · dsimp only [Iso.trans_hom]
    simp only [Category.assoc]
    rw [← unitAction_naturality d.symm ((e.hom ⊗ₘ e.hom) ≫ (λ_ (𝟙_ B)).hom),
      unitAction_unit]
    change (t (𝟙_ A) (𝟙_ A)).hom ≫
      ((e.hom ⊗ₘ e.hom) ≫ (λ_ (𝟙_ B)).hom) ≫ d.inv = _
    apply (cancel_mono d.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    dsimp only [d, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorIso_hom, tensorIso]
    simp only [← G.map_comp_assoc, Iso.hom_inv_id, G.map_id,
      Iso.hom_inv_id_assoc, Category.id_comp]
end UnitAction

/-- Normalize the comparison at the specified unit isomorphism.
Source: Stacks Project, sites-modules.tex, Tag 03EL.
Proof: the composite from the target unit through v inverse, F of the inverse unitor,
the tensor comparison, v tensor v and the target unitor is a unit automorphism q.
Postcompose the tensor comparison by the natural action of q inverse on its target.
The action at the unit is q inverse, so naturality and cancellation give the normalized
unit equation. The action is defined by conjugating q inverse tensor identity by unitors.
(blueprint: lem-weil-pbc-cech-pullback-normalized-coherence) -/
theorem cech_pullback_normalized_coherence
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (h : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (F : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    [F.PreservesZeroMorphisms] (_hF : F ⊣ h.modules)
    (v : F.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (coh : @TensorCoherence _ _ _ _
      (SheafOfModules.monoidalCategory R) (SheafOfModules.monoidalCategory S) F
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) v) :
    ∃ t : ∀ X Y, F.obj (@MonoidalCategory.tensorObj _ _
        (SheafOfModules.monoidalCategory R).toMonoidalCategoryStruct X Y) ≅
      @MonoidalCategory.tensorObj _ _
        (SheafOfModules.monoidalCategory S).toMonoidalCategoryStruct (F.obj X) (F.obj Y),
      (letI := SheafOfModules.monoidalCategory R
       letI := SheafOfModules.monoidalCategory S
       (∀ {X X' Y Y'} (f : X ⟶ X') (g : Y ⟶ Y'),
         F.map (f ⊗ₘ g) ≫ (t X' Y').hom =
           (t X Y).hom ≫ (F.map f ⊗ₘ F.map g)) ∧
       ((t (𝟙_ _) (𝟙_ _)).hom ≫ (v.hom ⊗ₘ v.hom) ≫ (λ_ (𝟙_ _)).hom =
         F.map (λ_ (𝟙_ _)).hom ≫ v.hom)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  exact normalizeTensor F v coh.tensor coh.naturality
end CategoryTheory
