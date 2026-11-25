/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldScalarExtension

/-! # The scalar-extension adjunction

Source: Stacks Project, Sheaves on Spaces, Tags 0095 and 0096.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafOfModules

variable {k : Type u} [Ring k] (X : TopCat.{u})
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (α : k →+* R.obj.obj (op ⊤))

private noncomputable def scalarRestrictionHomEquiv
    (V : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{max u v} k))
    (M : SheafOfModules.{max u v} R) :
    ((modulePresheafToConstantModules.{u, v} X).obj V.obj ⟶
      (PresheafOfModules.pushforward.{max u v} (fieldScalarPresheafRingMap X R α)).obj M.val) ≃
    (V ⟶ (forgetToSheafModuleCat R (op ⊤) isTerminalTop.op ⋙
      sheafCompose _ (ModuleCat.restrictScalars α)).obj M) where
  toFun f :=
    { hom :=
        { app := fun U ↦ ModuleCat.ofHom
            (X := V.obj.obj U)
            (Y := ((forgetToSheafModuleCat R (op ⊤) isTerminalTop.op ⋙
              sheafCompose _ (ModuleCat.restrictScalars α)).obj M).obj.obj U)
            { toFun := f.app U
              map_add' := (f.app U).hom.map_add
              map_smul' := (f.app U).hom.map_smul }
          naturality := fun _ _ g ↦ by
            ext a
            exact PresheafOfModules.naturality_apply f g a } }
  invFun f :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((modulePresheafToConstantModules.{u, v} X).obj V.obj).obj U)
        (Y := ((PresheafOfModules.pushforward
          (fieldScalarPresheafRingMap X R α)).obj M.val).obj U)
        { toFun := f.hom.app U
          map_add' := (f.hom.app U).hom.map_add
          map_smul' := (f.hom.app U).hom.map_smul }
      naturality := fun g ↦ by
        ext a
        exact ConcreteCategory.congr_hom (f.hom.naturality g) a }
  left_inv f := by ext U a; rfl
  right_inv f := by ext U a; rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor extension followed by sheafification is left adjoint to scalar restriction.

Source: Stacks Project, Sheaves on Spaces, Tags 0095 and 0096.
(blueprint: lem-sc-field-scalar-extension-adjunction).

Proof: regard a k-module-valued presheaf as modules over the constant presheaf k.
Apply the presheaf pullback/pushforward adjunction for the map k -> R and then
sheafification's adjunction. Morphisms into the pushforward are exactly natural
k-linear maps to the scalar restriction. The two bijections are natural in both
arguments, so their composite is the required adjunction. This uses only rings,
not the field hypothesis. -/
theorem nonempty_fieldScalarExtensionAdjunction :
    Nonempty (fieldScalarExtension.{u, v} X R α ⊣
      forgetToSheafModuleCat R (op ⊤) isTerminalTop.op ⋙
        sheafCompose _ (ModuleCat.restrictScalars α)) := by
  let := fieldScalarPresheafPullback_isRightAdjoint.{u, v} X R α
  let := fieldScalarExtension_hasSheafify.{u, v} X
  let := fieldScalarExtension_wEqualsLocallyBijective.{u, v} X
  refine ⟨Adjunction.mkOfHomEquiv
    { homEquiv := fun V M ↦
        ((PresheafOfModules.sheafificationAdjunction.{max u v} (𝟙 R.obj)).homEquiv _ _).trans
          (((PresheafOfModules.pullbackPushforwardAdjunction.{max u v}
            (fieldScalarPresheafRingMap X R α)).homEquiv _ _).trans
            (scalarRestrictionHomEquiv.{u, v} X R α V M))
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }⟩
  · intro V' V M f g
    dsimp only [fieldScalarExtension, Functor.comp_obj, Functor.comp_map]
    dsimp only [Equiv.symm_trans, Equiv.trans_apply]
    erw [show (scalarRestrictionHomEquiv.{u, v} X R α V' M).symm (f ≫ g) =
        (modulePresheafToConstantModules.{u, v} X).map f.hom ≫
          (scalarRestrictionHomEquiv.{u, v} X R α V M).symm g from by
          apply PresheafOfModules.hom_ext
          intro U
          ext a
          rfl]
    erw [Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_naturality_left_symm]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  · intro V M M' f g
    dsimp only [Equiv.trans_apply]
    erw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_right]
    ext U a
    rfl

end SheafOfModules
