/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom

/-!
# The internal hom out of the unit, and additivity of the internal hom

Let `R : Cᵒᵖ ⥤ CommRingCat` be a presheaf of commutative rings on a category `C`. For a presheaf
of modules `N` over `R`, the internal hom `homObj R N` out of the unit is `N`
(`PresheafOfModules.homObjUnitIso`): a morphism `R|_U ⟶ N|_U` is determined by the image of `1`.
The internal hom is additive in its first variable (`PresheafOfModules.homObjMap_add_left`).
-/

@[expose] public section


universe v v₁ u₁ u

open CategoryTheory Opposite

namespace PresheafOfModules

section Additive

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable {M M' N N' : PresheafOfModules.{v} (R ⋙ forget₂ _ _)}

lemma homObjMap_add_left (f f' : M' ⟶ M) (g : N ⟶ N') :
    homObjMap (f + f') g = homObjMap f g + homObjMap f' g := by
  ext X φ : 3
  exact Preadditive.add_comp _ _ _ ((restrictOver R X.unop).map f)
    ((restrictOver R X.unop).map f') _

lemma homObjMap_zero_left (g : N ⟶ N') : homObjMap (0 : M' ⟶ M) g = 0 := by
  ext X φ : 3
  change (restrictOver R X.unop).map (0 : M' ⟶ M) ≫ φ ≫ (restrictOver R X.unop).map g = 0
  rw [show (restrictOver R X.unop).map (0 : M' ⟶ M) = 0 from by ext; rfl, Limits.zero_comp]

lemma restrictOver_smul_app_apply {M P : PresheafOfModules.{v} (R ⋙ forget₂ _ _)}
    {U : C} (r : R.obj (op U)) (φ : (restrictOver R U).obj M ⟶ (restrictOver R U).obj P)
    (W : (Over U)ᵒᵖ) (x : M.obj (op W.unop.left)) :
    (r • φ).app W x = R.map W.unop.hom.op r • show P.obj (op W.unop.left) from φ.app W x :=
  rfl

end Additive


section Unit

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

/-- A section `n` of `N` over `U` gives the morphism `R|_U ⟶ N|_U`, `r ↦ r • n`. -/
noncomputable def homObjUnitInvApp {U : C} (n : N.obj (op U)) :
    (restrictOver R U).obj (unit _) ⟶ (restrictOver R U).obj N :=
  (unitHomEquiv ((restrictOver R U).obj N)).symm
    (sectionsMk (fun W ↦ N.map W.unop.hom.op n) fun {W W'} f ↦ by
      change N.map f.unop.left.op (N.map W.unop.hom.op n) = N.map W'.unop.hom.op n
      rw [← map_comp_apply, ← op_comp, Over.w])

lemma homObjUnitInvApp_app_apply {U : C} (n : N.obj (op U)) (W : (Over U)ᵒᵖ)
    (r : R.obj (op W.unop.left)) :
    (homObjUnitInvApp N n).app W r = r • (show N.obj (op W.unop.left) from N.map W.unop.hom.op n) :=
  rfl

lemma map_id_apply' {X : Cᵒᵖ} (x : N.obj X) : N.map (𝟙 X) x = x := by
  rw [map_id]
  rfl

lemma homObjUnitInvApp_app_one {U : C} (n : N.obj (op U)) :
    (homObjUnitInvApp N n).app (op (Over.mk (𝟙 U))) (1 : R.obj (op U)) = n :=
  (congrArg (fun s ↦ s.val (op (Over.mk (𝟙 U))))
    ((unitHomEquiv ((restrictOver R U).obj N)).apply_symm_apply _)).trans
      ((N.congr_map_apply op_id n).trans (N.map_id_apply' n))


/-- The `R(X)`-module structure on the sections of `homObj M N` over `X`, stated for the ring
`(R ⋙ forget₂ _ _).obj X` so that `ModuleCat.ofHom` finds it. -/
noncomputable instance instModuleHomObjSections {M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (X : Cᵒᵖ) :
    Module ((R ⋙ forget₂ CommRingCat RingCat).obj X)
      ((restrictOver R X.unop).obj M ⟶ (restrictOver R X.unop).obj N) :=
  inferInstanceAs (Module (R.obj (op X.unop)) _)

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- The sections of `homObj R N` over `X` are the sections of `N` over `X`. -/
noncomputable def homObjUnitIsoApp (X : Cᵒᵖ) : (homObj (unit _) N).obj X ≅ N.obj X :=
    { hom := ModuleCat.ofHom
        { toFun φ := φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop))
          map_add' _ _ := rfl
          map_smul' r φ := by
            refine (restrictOver_smul_app_apply r φ _ _).trans ?_
            change R.map (𝟙 _) r • _ = _
            rw [R.map_id]
            rfl }
      inv := ModuleCat.ofHom
        { toFun n := homObjUnitInvApp N n
          map_add' n n' := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) •
                (show N.obj (op W.unop.left) from N.map W.unop.hom.op (n + n')) =
                (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op n) +
                  (1 : R.obj (op W.unop.left)) •
                    (show N.obj (op W.unop.left) from N.map W.unop.hom.op n')
              rw [map_add, smul_add]
          map_smul' r n := hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
            (M₂ := (restrictOver R X.unop).obj N) fun W ↦ by
              ext
              change (1 : R.obj (op W.unop.left)) •
                (show N.obj (op W.unop.left) from N.map W.unop.hom.op (r • n)) =
                R.map W.unop.hom.op r • (1 : R.obj (op W.unop.left)) •
                  (show N.obj (op W.unop.left) from N.map W.unop.hom.op n)
              rw [one_smul, one_smul, N.map_smul]
              rfl }
      hom_inv_id := by
        ext φ : 2
        refine hom_ext (M₁ := (restrictOver R X.unop).obj (unit _))
          (M₂ := (restrictOver R X.unop).obj N) fun W ↦ ?_
        refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
        change (1 : R.obj (op W.unop.left)) • N.map W.unop.hom.op
          (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj (op X.unop))) =
            φ.app W (1 : R.obj (op W.unop.left))
        rw [one_smul]
        refine (naturality_apply φ
          (Over.homMk W.unop.hom (Category.comp_id _) : W.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj (op X.unop))).symm.trans ?_
        exact congrArg (φ.app W) (unit_map_one (R := R ⋙ forget₂ _ _) W.unop.hom.op)
      inv_hom_id := by
        ext n
        exact homObjUnitInvApp_app_one N n }


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
lemma homObjUnitIsoApp_hom_apply (X : Cᵒᵖ) (φ : (homObj (unit _) N).obj X) :
    (homObjUnitIsoApp N X).hom φ = φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj X) :=
  rfl

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- **The internal hom out of the unit.** `homObj R N ≅ N`: a morphism `R|_U ⟶ N|_U` is
determined by the image of `1`. -/
noncomputable def homObjUnitIso : homObj (unit _) N ≅ N :=
  isoMk (homObjUnitIsoApp N) fun X Y g ↦ by
    ext φ
    change φ.app (op (Over.mk (𝟙 Y.unop ≫ g.unop))) (1 : R.obj Y) =
      N.map g (φ.app (op (Over.mk (𝟙 X.unop))) (1 : R.obj X))
    refine (restrictOver_hom_app_congr (M := unit _) (N := N) φ (Category.id_comp g.unop)
      (1 : R.obj Y)).trans (Eq.trans ?_ (naturality_apply φ
        (Over.homMk g.unop (Category.comp_id _) : Over.mk g.unop ⟶ Over.mk (𝟙 X.unop)).op
          (1 : R.obj X)))
    exact congrArg (φ.app _) (unit_map_one (R := R ⋙ forget₂ _ _) g).symm

end Unit

end PresheafOfModules
