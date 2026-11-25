/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom

/-!
# Restricting the internal hom of presheaves of modules

Let `R : Cᵒᵖ ⥤ CommRingCat` be a presheaf of commutative rings on a category `C`, and `U : C`.
For presheaves of modules `M` and `N` over `R`, the restriction of the internal hom `homObj M N`
to `Over U` is the internal hom of the restrictions of `M` and `N` to `Over U`
(`PresheafOfModules.restrictOverHomObjIso`). On sections over `W : Over U` this is the
identification of `Hom(M|_{W.left}, N|_{W.left})` with `Hom((M|_U)|_W, (N|_U)|_W)` given by
the equivalence `Over W ≌ Over W.left` (`CategoryTheory.Over.iteratedSliceEquiv`).
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _)} {U : C}

variable (U) in
/-- The forward map of `restrictOverHomObjIso` on sections over `W : Over U`: a morphism between
the restrictions of `M` and `N` to `Over W.left` gives a morphism between the restrictions of
`M|_U` and `N|_U` to `Over W`, by precomposition with `Over W ⥤ Over W.left`. -/
noncomputable def restrictOverHomObjFwd (W : Over U)
    (φ : (restrictOver R W.left).obj M ⟶ (restrictOver R W.left).obj N) :
    (restrictOver ((Over.forget U).op ⋙ R) W).obj ((restrictOver R U).obj M) ⟶
      (restrictOver ((Over.forget U).op ⋙ R) W).obj ((restrictOver R U).obj N) :=
  (pushforward₀ (Over.iteratedSliceForward W) _).map φ

@[simp]
lemma restrictOverHomObjFwd_app (W : Over U)
    (φ : (restrictOver R W.left).obj M ⟶ (restrictOver R W.left).obj N) (V : (Over W)ᵒᵖ) :
    (restrictOverHomObjFwd U W φ).app V = φ.app (op (Over.mk V.unop.hom.left)) :=
  rfl

variable (U) in
/-- The inverse map of `restrictOverHomObjIso` on sections over `W : Over U`. -/
noncomputable def restrictOverHomObjBwd (W : Over U)
    (ψ : (restrictOver ((Over.forget U).op ⋙ R) W).obj ((restrictOver R U).obj M) ⟶
      (restrictOver ((Over.forget U).op ⋙ R) W).obj ((restrictOver R U).obj N)) :
    (restrictOver R W.left).obj M ⟶ (restrictOver R W.left).obj N :=
  (pushforward₀ (Over.iteratedSliceBackward W) _).map ψ

@[simp]
lemma restrictOverHomObjBwd_app (W : Over U)
    (ψ : (restrictOver ((Over.forget U).op ⋙ R) W).obj ((restrictOver R U).obj M) ⟶
      (restrictOver ((Over.forget U).op ⋙ R) W).obj ((restrictOver R U).obj N))
    (V : (Over W.left)ᵒᵖ) :
    (restrictOverHomObjBwd U W ψ).app V = ψ.app (op ((Over.iteratedSliceBackward W).obj V.unop)) :=
  rfl

lemma restrictOverHomObjBwd_fwd (W : Over U)
    (φ : (restrictOver R W.left).obj M ⟶ (restrictOver R W.left).obj N) :
    restrictOverHomObjBwd U W (restrictOverHomObjFwd U W φ) = φ :=
  rfl

lemma restrictOverHomObjFwd_bwd (W : Over U)
    (ψ : (restrictOver ((Over.forget U).op ⋙ R) W).obj ((restrictOver R U).obj M) ⟶
      (restrictOver ((Over.forget U).op ⋙ R) W).obj ((restrictOver R U).obj N)) :
    restrictOverHomObjFwd U W (restrictOverHomObjBwd U W ψ) = ψ := by
  ext V x
  -- `V` and `Bwd (Fwd V)` only differ by the structure morphism of their underlying object of
  -- `Over U`, and `ψ` is natural with respect to the morphism between them whose underlying
  -- morphism in `C` is the identity.
  let e : (Over.iteratedSliceBackward W).obj ((Over.iteratedSliceForward W).obj V.unop) ⟶
      V.unop :=
    Over.homMk (Over.homMk (𝟙 V.unop.left.left)
      ((Category.id_comp _).trans (Over.w V.unop.hom).symm)) (by ext; exact Category.id_comp _)
  have he (P : PresheafOfModules.{v} (R ⋙ forget₂ _ _)) (y : P.obj (op V.unop.left.left)) :
      ((restrictOver ((Over.forget U).op ⋙ R) W).obj ((restrictOver R U).obj P)).map e.op y =
        y := by
    change P.map (𝟙 (op V.unop.left.left)) y = y
    rw [PresheafOfModules.map_id]
    rfl
  exact (congrArg (ψ.app (op ((Over.iteratedSliceBackward W).obj
    ((Over.iteratedSliceForward W).obj V.unop)))) (he M x).symm).trans
      ((naturality_apply ψ e.op x).trans (he N _))

variable (M N U) in
/-- **Restricting the internal hom.** The restriction of `homObj M N` to `Over U` is the internal
hom of the restrictions of `M` and `N` to `Over U`. -/
noncomputable def restrictOverHomObjIso :
    (restrictOver R U).obj (homObj M N) ≅
      homObj ((restrictOver R U).obj M) ((restrictOver R U).obj N) :=
  isoMk (fun W ↦
    { hom := ConcreteCategory.ofHom
        { toFun := restrictOverHomObjFwd U W.unop
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      inv := ConcreteCategory.ofHom
        { toFun := restrictOverHomObjBwd U W.unop
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      hom_inv_id := by ext φ : 2; exact restrictOverHomObjBwd_fwd W.unop φ
      inv_hom_id := by ext ψ : 2; exact restrictOverHomObjFwd_bwd W.unop ψ })
    (fun _ _ _ ↦ rfl)

lemma restrictOverHomObjIso_hom_app_apply (W : (Over U)ᵒᵖ)
    (φ : (restrictOver R W.unop.left).obj M ⟶ (restrictOver R W.unop.left).obj N) :
    (restrictOverHomObjIso M N U).hom.app W φ = restrictOverHomObjFwd U W.unop φ :=
  rfl

lemma restrictOverHomObjIso_inv_app_apply (W : (Over U)ᵒᵖ)
    (ψ : (restrictOver ((Over.forget U).op ⋙ R) W.unop).obj ((restrictOver R U).obj M) ⟶
      (restrictOver ((Over.forget U).op ⋙ R) W.unop).obj ((restrictOver R U).obj N)) :
    (restrictOverHomObjIso M N U).inv.app W ψ = restrictOverHomObjBwd U W.unop ψ :=
  rfl


end PresheafOfModules
