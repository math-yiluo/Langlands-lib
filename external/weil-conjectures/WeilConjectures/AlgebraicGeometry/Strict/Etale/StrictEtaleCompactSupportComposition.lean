/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientTransportInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleTransportAssociator
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleInverseTransportComposition

/-! # Composition of normalized compact-support coefficient projections

Source: Zheng, Construction 5.15 and Proposition 2.29(2).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
section
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  {G G' : C ⥤ E} {H H' : D ⥤ F}

end

section Three
variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type u₁}
  [Category.{v₁} C₁] [Category.{v₁} C₂] [Category.{v₁} C₃]
  [Category.{v₁} D₁] [Category.{v₁} D₂] [Category.{v₁} D₃]
  {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
  {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
  {L₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
  {G₁₂ : C₁ ⥤ C₂} {G₂₃ : C₂ ⥤ C₃} {G₁₃ : C₁ ⥤ C₃}
  {H₁₂ : D₁ ⥤ D₂} {H₂₃ : D₂ ⥤ D₃} {H₁₃ : D₁ ⥤ D₃}

end Three

section Pasting
variable {C₁ C₂ C₃ D₁ D₂ D₃ E₁ E₂ E₃ : Type u₁}
  [Category.{v₁} C₁] [Category.{v₁} C₂] [Category.{v₁} C₃]
  [Category.{v₁} D₁] [Category.{v₁} D₂] [Category.{v₁} D₃]
  [Category.{v₁} E₁] [Category.{v₁} E₂] [Category.{v₁} E₃]
  {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {F₃ : C₃ ⥤ D₃}
  {R₁ : D₁ ⥤ E₁} {R₂ : D₂ ⥤ E₂} {R₃ : D₃ ⥤ E₃}
  {X₁₂ : C₁ ⥤ C₂} {X₂₃ : C₂ ⥤ C₃} {X₁₃ : C₁ ⥤ C₃}
  {Z₁₂ : D₁ ⥤ D₂} {Z₂₃ : D₂ ⥤ D₃} {Z₁₃ : D₁ ⥤ D₃}
  {Y₁₂ : E₁ ⥤ E₂} {Y₂₃ : E₂ ⥤ E₃} {Y₁₃ : E₁ ⥤ E₃}

private def projectionIso
    (A : X₁₂ ⋙ F₂ ≅ F₁ ⋙ Z₁₂) (B : R₁ ⋙ Y₁₂ ≅ Z₁₂ ⋙ R₂) :
    (F₁ ⋙ R₁) ⋙ Y₁₂ ≅ X₁₂ ⋙ (F₂ ⋙ R₂) :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ B ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight A.symm _ ≪≫
      Functor.associator _ _ _

private theorem projection_composition
    (A₁₂ : X₁₂ ⋙ F₂ ≅ F₁ ⋙ Z₁₂) (A₂₃ : X₂₃ ⋙ F₃ ≅ F₂ ⋙ Z₂₃)
    (A₁₃ : X₁₃ ⋙ F₃ ≅ F₁ ⋙ Z₁₃)
    (B₁₂ : R₁ ⋙ Y₁₂ ≅ Z₁₂ ⋙ R₂) (B₂₃ : R₂ ⋙ Y₂₃ ≅ Z₂₃ ⋙ R₃)
    (B₁₃ : R₁ ⋙ Y₁₃ ≅ Z₁₃ ⋙ R₃)
    (AX : X₁₂ ⋙ X₂₃ ⟶ X₁₃) (AY : Y₁₂ ⋙ Y₂₃ ⟶ Y₁₃)
    (AZ : Z₁₂ ⋙ Z₂₃ ⟶ Z₁₃)
    (hopen : ∀ K, F₃.map (AX.app K) ≫ A₁₃.hom.app K =
      A₂₃.hom.app (X₁₂.obj K) ≫ Z₂₃.map (A₁₂.hom.app K) ≫ AZ.app (F₁.obj K))
    (hproper : ∀ K, R₃.map (AZ.app K) ≫ B₁₃.inv.app K =
      B₂₃.inv.app (Z₁₂.obj K) ≫ Y₂₃.map (B₁₂.inv.app K) ≫ AY.app (R₁.obj K))
    (K) :
    (F₃ ⋙ R₃).map (AX.app K) ≫ (projectionIso A₁₃ B₁₃).inv.app K =
      (projectionIso A₂₃ B₂₃).inv.app (X₁₂.obj K) ≫
        Y₂₃.map ((projectionIso A₁₂ B₁₂).inv.app K) ≫ AY.app ((F₁ ⋙ R₁).obj K) := by
  simp only [projectionIso, Iso.trans_inv, NatTrans.comp_app, associator_inv_app,
    associator_hom_app, isoWhiskerRight_inv, isoWhiskerLeft_inv, Iso.symm_inv,
    whiskerRight_app, whiskerLeft_app, Functor.comp_obj, Functor.comp_map,
    Category.comp_id, Category.id_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, hopen]
  simp only [Functor.map_comp, Category.assoc]
  rw [hproper]
  have hn : R₃.map (Z₂₃.map (A₁₂.hom.app K)) ≫
      B₂₃.inv.app (Z₁₂.obj (F₁.obj K)) =
      B₂₃.inv.app (F₂.obj (X₁₂.obj K)) ≫ Y₂₃.map (R₂.map (A₁₂.hom.app K)) :=
    B₂₃.inv.naturality (A₁₂.hom.app K)
  rw [← Category.assoc (R₃.map (Z₂₃.map (A₁₂.hom.app K))), hn]
  simp only [Category.assoc]

end Pasting

end AlgebraicGeometry
