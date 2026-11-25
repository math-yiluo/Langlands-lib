/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Mates of mates in a square of adjunctions

Consider four adjunctions `Ψ_Y ⊣ Res_Y`, `Ψ_Z ⊣ Res_Z`, `L_R ⊣ P_R` and `L_S ⊣ P_S`
forming a square, an isomorphism `γ : Ψ_Y ⋙ L_S ≅ L_R ⋙ Ψ_Z`, its mate
`c : Res_Y ⋙ L_R ⟶ L_S ⋙ Res_Z` along the adjunctions `Ψ ⊣ Res`, and an isomorphism
`α : Res_Z ⋙ P_R ≅ P_S ⋙ Res_Y` whose inverse is the mate of `c` along the adjunctions
`L ⊣ P`. Then the mate `β : P_R ⋙ Ψ_Y ⟶ Ψ_Z ⋙ P_S` of `γ` along the adjunctions `L ⊣ P` is
the transpose along `Ψ ⊣ Res` of `P_R η ≫ α`
(`CategoryTheory.Adjunction.unit_app_comp_map_mateEquiv_app`).

The intended case: `Ψ` is extension of scalars along a ring map `R ⟶ S`, `Res` restriction of
scalars, and `L ⊣ P` is the derived pullback–pushforward adjunction.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {YR YS ZR ZS : Type*} [Category YR] [Category YS] [Category ZR] [Category ZS]
  {ΨY : YR ⥤ YS} {ResY : YS ⥤ YR} (aY : ΨY ⊣ ResY)
  {ΨZ : ZR ⥤ ZS} {ResZ : ZS ⥤ ZR} (aZ : ΨZ ⊣ ResZ)
  {LR : YR ⥤ ZR} {PR : ZR ⥤ YR} (adjR : LR ⊣ PR)
  {LS : YS ⥤ ZS} {PS : ZS ⥤ YS} (adjS : LS ⊣ PS)

/-- The mate `β` of `γ` along the adjunctions `L ⊣ P` is the transpose along `Ψ ⊣ Res` of
`P_R η ≫ α`, when `c` is the mate of `γ⁻¹` along `Ψ ⊣ Res` and `α⁻¹` the mate of `c` along
`L ⊣ P`. -/
lemma unit_app_comp_map_mateEquiv_app (γ : ΨY ⋙ LS ≅ LR ⋙ ΨZ)
    (c : ResY ⋙ LR ⟶ LS ⋙ ResZ) (hc : mateEquiv aY aZ γ.inv = c)
    (α : ResZ ⋙ PR ≅ PS ⋙ ResY) (hα : mateEquiv adjS adjR c = α.inv) (K : ZR) :
    aY.unit.app (PR.obj K) ≫ ResY.map ((mateEquiv adjR adjS γ.hom).app K) =
      PR.map (aZ.unit.app K) ≫ α.hom.app (ΨZ.obj K) := by
  rw [← cancel_mono (α.inv.app (ΨZ.obj K))]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rw [← hα, ← hc]
  simp only [Functor.id_obj, Functor.comp_obj, mateEquiv_apply, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp, Functor.map_comp,
    Functor.whiskerRight_comp, Functor.whiskerRight_twice, Category.assoc,
    Functor.whiskerLeft_comp, Functor.map_id]
  set x := PR.obj K
  set W := ResY.obj (PS.obj (ΨZ.obj K))
  set f : x ⟶ W := aY.unit.app x ≫ ResY.map (adjS.unit.app (ΨY.obj x)) ≫
    ResY.map (PS.map ((γ.hom).app x)) ≫
      ResY.map (PS.map (ΨZ.map (adjR.counit.app K))) with hf
  have h₁ : ΨY.map f ≫ aY.counit.app (PS.obj (ΨZ.obj K)) =
      adjS.unit.app (ΨY.obj x) ≫ PS.map ((γ.hom).app x) ≫
        PS.map (ΨZ.map (adjR.counit.app K)) := by
    simp [hf]
  have h₂ : LS.map (ΨY.map f ≫ aY.counit.app (PS.obj (ΨZ.obj K))) ≫
      adjS.counit.app (ΨZ.obj K) =
      (γ.hom).app x ≫ ΨZ.map (adjR.counit.app K) := by
    rw [h₁]
    simp
  have h₃ : ΨZ.map (LR.map f) ≫ (γ.inv).app W ≫
      LS.map (aY.counit.app (PS.obj (ΨZ.obj K))) ≫ adjS.counit.app (ΨZ.obj K) =
      ΨZ.map (adjR.counit.app K) := by
    have := (γ.inv).naturality f
    dsimp at this
    rw [reassoc_of% this, ← LS.map_comp_assoc, h₂]
    have hγ : (γ.inv).app x ≫ (γ.hom).app x = 𝟙 _ :=
      NatTrans.congr_app γ.inv_hom_id x
    rw [reassoc_of% hγ]
  have h₄ : LR.map f ≫ aZ.unit.app (LR.obj W) ≫ ResZ.map ((γ.inv).app W) ≫
      ResZ.map (LS.map (aY.counit.app (PS.obj (ΨZ.obj K)))) ≫
        ResZ.map (adjS.counit.app (ΨZ.obj K)) =
      adjR.counit.app K ≫ aZ.unit.app K := by
    rw [← aZ.unit_naturality_assoc]
    simp only [← Functor.map_comp]
    rw [h₃]
    exact aZ.unit_naturality _
  have h₅ := congrArg PR.map h₄
  simp only [Functor.map_comp] at h₅
  calc _ = adjR.unit.app x ≫ PR.map (LR.map f) ≫ PR.map (aZ.unit.app (LR.obj W)) ≫
        PR.map (ResZ.map ((γ.inv).app W)) ≫
        PR.map (ResZ.map (LS.map (aY.counit.app (PS.obj (ΨZ.obj K))))) ≫
        PR.map (ResZ.map (adjS.counit.app (ΨZ.obj K))) := by
          exact ((adjR.unit_naturality_assoc f _).trans
            (by simp only [hf, Category.assoc]; rfl)).symm
    _ = _ := by rw [h₅, adjR.right_triangle_components_assoc]

end CategoryTheory.Adjunction
