/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Internal Hom under the open-subscheme equivalence

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Mathlib AlgebraicGeometry/Modules/Sheaf.lean, `overEquiv`.
(blueprint: lem-sc-internal-hom-over-equiv). -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Reindex local linear maps along the open-site equivalence.
Source: Stacks Project, Cohomology, Tag 08DL; Mathlib `overEquiv`. -/
private noncomputable def internalHomOverEquivMap {Y : Scheme.{u}} (U : Y.Opens)
    (A B : SheafOfModules.{u} (Y.ringCatSheaf.over U)) :
    (Scheme.Modules.overEquiv U).functor.obj
      (SheafOfModules.homObj (R := Y.toRingedSpace.sheaf.over U) A B) ⟶
    SheafOfModules.homObj (R := U.toScheme.toRingedSpace.sheaf)
      ((Scheme.Modules.overEquiv U).functor.obj A)
      ((Scheme.Modules.overEquiv U).functor.obj B) := by
  refine ⟨{ app := fun V ↦ ?_, naturality := ?_ }⟩
  · refine ConcreteCategory.ofHom (C := ModuleCat _)
      { toFun := fun φ ↦ ?_, map_add' := ?_, map_smul' := ?_ }
    · refine { app := fun W ↦ ?_, naturality := ?_ }
      · exact φ.app (Opposite.op ((Over.post U.overEquivalence.inverse).obj W.unop))
      · intro W W' h
        ext x
        exact PresheafOfModules.naturality_apply φ
          ((Over.post U.overEquivalence.inverse).map h.unop).op x
    · intros
      apply PresheafOfModules.hom_ext
      intro W
      ext x
      rfl
    · intros
      apply PresheafOfModules.hom_ext
      intro W
      ext x
      rfl
  · intro V V' h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    rfl
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem internalHomOverEquivMap_injective {Y : Scheme.{u}} (U : Y.Opens)
    (A B : SheafOfModules.{u} (Y.ringCatSheaf.over U))
    (V : U.toScheme.Opensᵒᵖ) :
    Function.Injective ((internalHomOverEquivMap U A B).val.app V) := by
  intro φ ψ h
  let H := Over.post U.overEquivalence.inverse (X := V.unop)
  let Q := (Functor.whiskeringLeft _ _ AddCommGrpCat).obj H.op
  apply (PresheafOfModules.toPresheaf _).map_injective
  apply Q.map_injective
  ext W x
  exact congrArg (fun t ↦ t.app W x) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem internalHomOverEquivMap_surjective {Y : Scheme.{u}} (U : Y.Opens)
    (A B : SheafOfModules.{u} (Y.ringCatSheaf.over U))
    (V : U.toScheme.Opensᵒᵖ) :
    Function.Surjective ((internalHomOverEquivMap U A B).val.app V) := by
  intro ψ
  let H := Over.post U.overEquivalence.inverse (X := V.unop)
  let Q := (Functor.whiskeringLeft _ _ AddCommGrpCat).obj H.op
  let M := (PresheafOfModules.restrictOver
    (Y.toRingedSpace.sheaf.over U).obj (U.overEquivalence.inverse.obj V.unop)).obj A.val
  let N := (PresheafOfModules.restrictOver
    (Y.toRingedSpace.sheaf.over U).obj (U.overEquivalence.inverse.obj V.unop)).obj B.val
  let t : M.presheaf ⟶ N.presheaf := Q.preimage ((PresheafOfModules.toPresheaf _).map ψ)
  have ht := Q.map_preimage (X := M.presheaf) (Y := N.presheaf)
    ((PresheafOfModules.toPresheaf _).map ψ)
  have htlin (W : (Over V.unop)ᵒᵖ)
      (r : ((Y.toRingedSpace.sheaf.over U).obj.obj
        (Opposite.op (H.obj W.unop).left))) (m : M.obj (H.op.obj W)) :
      t.app (H.op.obj W) (r • m) = r • (show N.obj (H.op.obj W) from t.app (H.op.obj W) m) := by
    have he := NatTrans.congr_app ht W
    have hval (x : M.obj (H.op.obj W)) : t.app (H.op.obj W) x = ψ.app W x :=
      ConcreteCategory.congr_hom he x
    exact (hval (r • m)).trans ((ψ.app W).hom.map_smul r m |>.trans
      (congrArg (fun x : N.obj (H.op.obj W) ↦ r • x) (hval m).symm))
  refine ⟨PresheafOfModules.homMk t ?_, ?_⟩
  · intro W r m
    let W' := H.op.objPreimage W
    let e := H.op.objObjPreimageIso W
    let S := (Over.forget (U.overEquivalence.inverse.obj V.unop)).op ⋙
      (Y.toRingedSpace.sheaf.over U).obj
    have hinj : Function.Injective (N.presheaf.map e.inv) :=
      ((ConcreteCategory.isIso_iff_bijective (N.presheaf.map e.inv)).1 (by
        infer_instance)).1
    apply hinj
    have hn (x : M.obj W) : N.map e.inv (t.app W x) =
        t.app (H.op.obj W') (M.map e.inv x) :=
      (ConcreteCategory.congr_hom (t.naturality e.inv) x).symm
    exact (hn (r • m)).trans <|
      (congrArg (fun x : M.obj (H.op.obj W') ↦ t.app (H.op.obj W') x)
        (M.map_smul e.inv r m)).trans <|
      (htlin W' (S.map e.inv r) (M.map e.inv m)).trans <|
      (congrArg (fun x : N.obj (H.op.obj W') ↦ S.map e.inv r • x) (hn m).symm).trans <|
      (N.map_smul e.inv r (t.app W m)).symm
  · apply PresheafOfModules.hom_ext
    intro W
    ext x
    exact ConcreteCategory.congr_hom (NatTrans.congr_app ht W) x

/-- The equivalence from the over-open site to the open subscheme preserves internal
Hom, naturally in both module arguments.

Source: Stacks Project, Cohomology, Tag 08DL, construction of internal Hom;
Mathlib AlgebraicGeometry/Modules/Sheaf.lean, `overEquiv`.
(blueprint: lem-sc-internal-hom-over-equiv).

Proof: An open V of U corresponds to its image open in Y equipped with the inclusion
into U. The slice over V is equivalent to the slice over that image object in the
over-U site: both describe the smaller opens contained in V, and the functors send
an inclusion to that same inclusion. A section of internal Hom is a compatible
family of local linear maps on this slice. Transport each map along this slice
equivalence and the structure-sheaf isomorphisms defining `overEquiv U`. These
isomorphisms transport scalars as well as the source and target modules, so the
transported maps are linear. The inverse transports them back. The two composites
are identities by cancellation of the scalar and module isomorphisms. Transport
commutes with restriction to a smaller open by naturality of these isomorphisms,
and with addition and scalar multiplication pointwise. Thus it defines an
isomorphism of sheaves of modules. Precomposition by f and postcomposition by g
commute with transport: in the expression for the three transported maps, the
intermediate module isomorphisms cancel. This is exactly the displayed naturality
equation. Empty opens and zero modules cause no exceptions: the same compatible
families and the same inverse constructions apply. This statement concerns only
module sheaves; it asserts neither product nor differential compatibility. -/
theorem internalHom_overEquiv {Y : Scheme.{u}} (U : Y.Opens) :
    let F := (Scheme.Modules.overEquiv U).functor
    ∃ e : ∀ (A B : SheafOfModules.{u} (Y.ringCatSheaf.over U)),
      F.obj (SheafOfModules.homObj (R := Y.toRingedSpace.sheaf.over U) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.toRingedSpace.sheaf) (F.obj A) (F.obj B),
      ∀ (A A' B B' : SheafOfModules.{u} (Y.ringCatSheaf.over U))
        (f : A' ⟶ A) (g : B ⟶ B'),
        F.map (SheafOfModules.homObjMap (R := Y.toRingedSpace.sheaf.over U) f g) ≫
            (e A' B').hom =
          (e A B).hom ≫
            SheafOfModules.homObjMap (R := U.toScheme.toRingedSpace.sheaf)
              (F.map f) (F.map g) := by
  let F := (Scheme.Modules.overEquiv U).functor
  have hi (A B : SheafOfModules.{u} (Y.ringCatSheaf.over U)) :
      IsIso (internalHomOverEquivMap U A B) := by
    let (V : U.toScheme.Opensᵒᵖ) :
        IsIso ((internalHomOverEquivMap U A B).val.app V) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (⟨internalHomOverEquivMap_injective U A B V,
        internalHomOverEquivMap_surjective U A B V⟩)
    let ep := PresheafOfModules.isoMk
      (fun V ↦ asIso ((internalHomOverEquivMap U A B).val.app V))
      (fun {_ _} h ↦ (internalHomOverEquivMap U A B).val.naturality h)
    let es := (SheafOfModules.fullyFaithfulForget U.toScheme.ringCatSheaf).preimageIso
      (X := F.obj (SheafOfModules.homObj (R := Y.toRingedSpace.sheaf.over U) A B))
      (Y := SheafOfModules.homObj (R := U.toScheme.toRingedSpace.sheaf)
        (F.obj A) (F.obj B)) ep
    have he : es.hom = internalHomOverEquivMap U A B := rfl
    rw [← he]
    infer_instance
  let e := fun A B ↦ asIso (internalHomOverEquivMap U A B)
  refine ⟨e, ?_⟩
  intro A A' B B' f g
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rfl

end AlgebraicGeometry
