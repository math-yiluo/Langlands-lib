/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Evaluation of a composite left-adjoint extension

Source: the horizontal composition law for adjunction mates, Stacks 0FND.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory
variable {X Y Z A B C : Type*}
  [Category X] [Category Y] [Category Z] [Category A] [Category B] [Category C]
  {F : X ⥤ Y} {U : Y ⥤ X} {G : Y ⥤ Z} {V : Z ⥤ Y} {H : X ⥤ Z} {W : Z ⥤ X}
  {Gx : X ⥤ A} {Gy : Y ⥤ B} {Gz : Z ⥤ C}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
  {L₃ : A ⥤ C} {R₃ : C ⥤ A}

/-- Evaluation of the canonical composite extension is the canonical scalar
associator. Source: Stacks 0FND
(blueprint: lem-pur-adjunction-evaluation-composition).
Proof: compare the inverses of the two isomorphisms and transpose through the total
scalar adjunction. The composite scalar transpose formula and the three evaluation
transpose equations identify both sides with the composite extension unit. The
right-square pasting law and naturality of the first right square move the intermediate
extension unit into this common expression. The normalized uniqueness equation for
the composite extension supplies its restriction compositor. -/
theorem adjunctionEvaluation_composition
    (af : F ⊣ U) (ag : G ⊣ V) (ah : H ⊣ W)
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
    (δe : V ⋙ U ≅ W) (δs : R₂ ⋙ R₁ ≅ R₃)
    (γ₁ : U ⋙ Gx ⟶ Gy ⋙ R₁) (γ₂ : V ⋙ Gy ⟶ Gz ⋙ R₂)
    (γ₃ : W ⋙ Gx ⟶ Gz ⋙ R₃)
    (ν₁ : F ⋙ Gy ≅ Gx ⋙ L₁) (ν₂ : G ⋙ Gz ≅ Gy ⋙ L₂)
    (ν₃ : H ⋙ Gz ≅ Gx ⋙ L₃)
    (hν₁ : ∀ P M (f : F.obj P ⟶ M), a₁.homEquiv _ _
      (ν₁.inv.app P ≫ Gy.map f) = Gx.map (af.homEquiv _ _ f) ≫ γ₁.app M)
    (hν₂ : ∀ P M (f : G.obj P ⟶ M), a₂.homEquiv _ _
      (ν₂.inv.app P ≫ Gz.map f) = Gy.map (ag.homEquiv _ _ f) ≫ γ₂.app M)
    (hν₃ : ∀ P M (f : H.obj P ⟶ M), a₃.homEquiv _ _
      (ν₃.inv.app P ≫ Gz.map f) = Gx.map (ah.homEquiv _ _ f) ≫ γ₃.app M)
    (hr : ∀ M, Gx.map (δe.hom.app M) ≫ γ₃.app M =
      γ₁.app (V.obj M) ≫ R₁.map (γ₂.app M) ≫ δs.hom.app (Gz.obj M)) (P : X) :
    Gz.map ((((af.comp ag).ofNatIsoRight δe).leftAdjointUniq ah).hom.app P) ≫
      ν₃.hom.app P =
    ν₂.hom.app (F.obj P) ≫ L₂.map (ν₁.hom.app P) ≫
      (((a₁.comp a₂).ofNatIsoRight δs).leftAdjointUniq a₃).hom.app (Gx.obj P) := by
  let e := ((af.comp ag).ofNatIsoRight δe).leftAdjointUniq ah
  let s := ((a₁.comp a₂).ofNatIsoRight δs).leftAdjointUniq a₃
  let i := Gz.mapIso (e.app P) ≪≫ ν₃.app P
  let j := ν₂.app (F.obj P) ≪≫ L₂.mapIso (ν₁.app P) ≪≫ s.app (Gx.obj P)
  have hi : i.inv = j.inv := by
    dsimp only [i, j, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv]
    simp only [Category.assoc]
    apply (a₃.homEquiv _ _).injective
    have h₁ := hν₁ P (F.obj P) (𝟙 _)
    have h₂ := hν₂ (F.obj P) (G.obj (F.obj P)) (𝟙 _)
    erw [Functor.map_id, Category.comp_id, Adjunction.homEquiv_id] at h₁ h₂
    have hs := adjunctionComposition_transpose a₁ a₂ a₃ δs (Gx.obj P)
      (Gy.obj (F.obj P)) (Gz.obj (G.obj (F.obj P)))
      (a₁.homEquiv _ _ (ν₁.inv.app P)) (a₂.homEquiv _ _ (ν₂.inv.app (F.obj P)))
    simp only [Equiv.symm_apply_apply] at hs
    erw [hν₃, hs, h₁, h₂]
    have he : ah.homEquiv _ _ (e.inv.app P) =
        af.unit.app P ≫ U.map (ag.unit.app (F.obj P)) ≫
          δe.hom.app (G.obj (F.obj P)) := by
      dsimp only [e]
      rw [Adjunction.leftAdjointUniq_inv_app,
        Adjunction.homEquiv_leftAdjointUniq_hom_app]
      rw [← ((af.comp ag).ofNatIsoRight δe).homEquiv_id P,
        Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
      change af.homEquiv P _ (ag.homEquiv _ _ (𝟙 _)) ≫ δe.hom.app _ = _
      rw [ag.homEquiv_id, af.homEquiv_unit, Category.assoc]
    rw [he]
    simp only [Functor.map_comp, Category.assoc]
    erw [hr]
    have hn := γ₁.naturality (ag.unit.app (F.obj P))
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
  have hij : i = j := Iso.ext_inv hi
  simpa only [i, j, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] using
    congrArg Iso.hom hij

end CategoryTheory
