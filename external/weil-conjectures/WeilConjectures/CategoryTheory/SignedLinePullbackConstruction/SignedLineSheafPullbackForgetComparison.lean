/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.Pullback
/-! # Forgetting algebraic structure in the constructed inverse image
Source: Stacks Project, Tags 00YV and 03D2.
(blueprint: lem-pur-signed-line-sheaf-pullback-forget).
-/
@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
universe u v w e
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory.SignedLinePullbackConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K]
  {E : Type e} [Category.{max u v w} E] (U : E ⥤ Type (max u v w))
  [∀ P : Cᵒᵖ ⥤ E, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K E] [J.HasSheafCompose U] [K.HasSheafCompose U]
  [K.PreservesSheafification U] [U.PreservesLeftKanExtensions F.op]
/-- The comparison obtained by commuting forgetting past sheafification and left Kan
extension. Both comparisons are the canonical ones, so they respect the units.
Source: Stacks Project, Tags 00YV and 03D2.
(blueprint: lem-pur-signed-line-sheaf-pullback-forget). -/
noncomputable def sheafPullbackForgetIso :
    sheafPullback F E J K ⋙ sheafCompose K U ≅
      sheafCompose J U ⋙ sheafPullback F (Type (max u v w)) J K :=
  NatIso.ofComponents (fun S ↦
    ((sheafComposeNatIso K U (sheafificationAdjunction K E)
      (sheafificationAdjunction K (Type (max u v w)))).app (F.op.lan.obj S.obj)).symm ≪≫
    (presheafToSheaf K (Type (max u v w))).mapIso
      ((U.lanCompIsoOfPreserves F.op).app S.obj))
    (by
      intro S T g
      change (presheafToSheaf K E ⋙ sheafCompose K U).map (F.op.lan.map g.hom) ≫
          (sheafComposeNatIso K U (sheafificationAdjunction K E)
            (sheafificationAdjunction K (Type (max u v w)))).inv.app _ ≫ _ = _
      rw [(sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K (Type (max u v w)))).inv.naturality_assoc]
      change _ ≫ (presheafToSheaf K (Type (max u v w))).map _ ≫
        (presheafToSheaf K (Type (max u v w))).map _ = _ ≫
        (presheafToSheaf K (Type (max u v w))).map _ ≫ (presheafToSheaf K (Type (max u v w))).map _
      simp only [← Functor.map_comp]
      congr 2
      exact (U.lanCompIsoOfPreserves F.op).hom.naturality g.hom)
/-- The underlying comparison sends the algebraic inverse-image unit to the set unit.
Source: Stacks Project, Tags 00YV and 03D2.
(blueprint: lem-pur-signed-line-sheaf-pullback-forget).
Proof: expand the composite adjunction unit. The sheafification comparison satisfies
its defining unit equation. Naturality of the set sheafification unit then moves the
Kan-extension comparison to the left, where its defining unit equation applies. -/
theorem sheafPullbackForgetIso_unit (S : Sheaf J E) :
    (sheafCompose J U).map ((sheafAdjunctionContinuous F E J K).unit.app S) ≫
      (F.sheafPushforwardContinuous (Type (max u v w)) J K).map
        ((sheafPullbackForgetIso J K F U).hom.app S) =
      (sheafAdjunctionContinuous F (Type (max u v w)) J K).unit.app
        ((sheafCompose J U).obj S) := by
  apply (sheafToPresheaf J (Type (max u v w))).map_injective
  simp only [Functor.map_comp]
  change Functor.whiskerRight ((sheafToPresheaf J E).map
      ((sheafAdjunctionContinuous F E J K).unit.app S)) U ≫ _ = _
  simp only [sheafAdjunctionContinuous, sheafPullback,
    Adjunction.map_restrictFullyFaithful_unit_app]
  dsimp only [Functor.comp_obj, Functor.id_obj, Iso.refl_hom, NatTrans.id_app]
  simp only [Functor.map_id, Category.comp_id]
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Category.comp_id]
  change Functor.whiskerRight ((F.op.lanAdjunction E).unit.app S.obj ≫
      Functor.whiskerLeft F.op ((sheafificationAdjunction K E).unit.app _)) U ≫
      Functor.whiskerLeft F.op
        (((sheafComposeNatIso K U (sheafificationAdjunction K E)
          (sheafificationAdjunction K (Type (max u v w)))).inv.app _).hom ≫
        ((presheafToSheaf K (Type (max u v w))).map
          ((U.lanCompIsoOfPreserves F.op).hom.app S.obj)).hom) =
    (F.op.lanAdjunction (Type (max u v w))).unit.app (S.obj ⋙ U) ≫
      Functor.whiskerLeft F.op ((sheafificationAdjunction K (Type (max u v w))).unit.app _)
  simp only [Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  have hs : Functor.whiskerRight
      ((sheafificationAdjunction K E).unit.app (F.op.lan.obj S.obj)) U ≫
      ((sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K (Type (max u v w)))).inv.app _).hom =
      (sheafificationAdjunction K (Type (max u v w))).unit.app (F.op.lan.obj S.obj ⋙ U) := by
    have h := sheafComposeNatTrans_fac K U (sheafificationAdjunction K E)
      (sheafificationAdjunction K (Type (max u v w))) (F.op.lan.obj S.obj)
    rw [← h]
    simp only [Category.assoc]
    change _ ≫ ((sheafToPresheaf K (Type (max u v w))).map
      ((sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K (Type (max u v w)))).hom.app _) ≫
      (sheafToPresheaf K (Type (max u v w))).map _) = _
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  have hn := (sheafificationAdjunction K (Type (max u v w))).unit.naturality
    ((U.lanCompIsoOfPreserves F.op).hom.app S.obj)
  have hk := U.leftKanExtensionCompIsoOfPreserves_hom_fac S.obj F.op
  ext V x
  have hs' := congrArg (fun t ↦ t.app (F.op.obj V)) hs
  have hn' := congrArg (fun t ↦ t.app (F.op.obj V)) hn
  have hk' := congrArg (fun t ↦ t.app V) hk
  simp only [Functor.lanAdjunction_unit] at hs' hn' hk' ⊢
  dsimp [Functor.lanCompIsoOfPreserves, Functor.lanUnit] at hs' hn' hk' ⊢
  simp only [Category.id_comp] at hk'
  have hsx := ConcreteCategory.congr_hom hs'
    ((U.map ((F.op.leftKanExtensionUnit S.obj).app V)) x)
  have hnx := ConcreteCategory.congr_hom hn'
    ((U.map ((F.op.leftKanExtensionUnit S.obj).app V)) x)
  have hkx := ConcreteCategory.congr_hom hk' x
  dsimp at hsx hnx hkx
  exact (congrArg (fun y ↦ (((presheafToSheaf K (Type (max u v w))).map
      (U.leftKanExtensionCompIsoOfPreserves S.obj F.op).hom).hom.app (F.op.obj V)) y)
    hsx).trans (hnx.symm.trans (congrArg (fun y ↦
      ((toSheafify K (F.op.leftKanExtension (S.obj ⋙ U))).app (F.op.obj V)) y) hkx))
end CategoryTheory.SignedLinePullbackConstruction
