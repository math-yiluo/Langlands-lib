/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-!
# Canonically normalized pro-etale module adjunctions

## References

* Stacks Project, Modules on Sites
* Cohomology on Sites, Tag 07A6
* Stacks, Tag 07A6 and Derived Categories, Tag 0DVC
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules

-- First transpose the sectionwise tensor maps, then use the sheafification adjunction.
-- These helpers work for sites in arbitrary object and morphism universes.

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}} (a : A ⟶ B)
set_option hygiene false in
local notation "𝓡" S => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S

private noncomputable local instance (M : SheafOfModules.{u} (𝓡 A))
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    Module (A.obj.obj V)
      ((ModuleCat.restrictScalars ((𝓡 A).obj.map i).hom).obj (M.val.obj V)) :=
  inferInstanceAs (Module (A.obj.obj V) (M.val.obj V))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem changeMap_tmul (M : SheafOfModules.{u} (𝓡 A)) {U V : Cᵒᵖ} (i : U ⟶ V)
    (b : B.obj.obj U) (m : M.val.obj U) :
    (changeOfRingsPresheaf a M).map i (b ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] m) =
      B.obj.map i b ⊗ₜ[A.obj.obj V, (a.hom.app V).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap a M i) b m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def tensorToRestrict (M : SheafOfModules.{u} (𝓡 A))
    (N : SheafOfModules.{u} (𝓡 B))
    (f : changeOfRingsPresheaf a M ⟶ N.val) :
    M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj N where
  val :=
    { app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (a.hom.app U).hom (f.app U)
      naturality := by
        intro U V i
        ext m
        change f.app V ((1 : B.obj.obj V) ⊗ₜ[A.obj.obj V,
          (a.hom.app V).hom] M.val.map i m) =
          N.val.map i (f.app U ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U,
            (a.hom.app U).hom] m))
        rw [← PresheafOfModules.naturality_apply f i]
        rw [changeMap_tmul]
        simp }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def tensorFromRestrict (M : SheafOfModules.{u} (𝓡 A))
    (N : SheafOfModules.{u} (𝓡 B))
    (g : M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj N) :
    changeOfRingsPresheaf a M ⟶ N.val where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    («R» := A.obj.obj U) («S» := B.obj.obj U) (a.hom.app U).hom (g.val.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      («R» := A.obj.obj V) («S» := B.obj.obj V) (a.hom.app V).hom (g.val.app V)
        ((changeOfRingsPresheaf a M).map i _) =
      N.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        («R» := A.obj.obj U) («S» := B.obj.obj U) (a.hom.app U).hom (g.val.app U) _)
    rw [changeMap_tmul]
    simp only [map_one]
    let : Module (A.obj.obj V) (B.obj.obj V) := Module.compHom _ (a.hom.app V).hom
    let : Module (A.obj.obj V) (N.val.obj V) := Module.compHom _ (a.hom.app V).hom
    let : Module (A.obj.obj U) (B.obj.obj U) := Module.compHom _ (a.hom.app U).hom
    let : Module (A.obj.obj U) (N.val.obj U) := Module.compHom _ (a.hom.app U).hom
    erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := A.obj.obj V) («S» := B.obj.obj V), TensorProduct.lift.tmul,
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := A.obj.obj U) («S» := B.obj.obj U), TensorProduct.lift.tmul]
    change (1 : B.obj.obj V) • (show N.val.obj V from g.val.app V (M.val.map i m)) =
      N.val.map i ((1 : B.obj.obj U) • (show N.val.obj U from g.val.app U m))
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply g.val i m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def tensorHomEquiv (M : SheafOfModules.{u} (𝓡 A))
    (N : SheafOfModules.{u} (𝓡 B)) :
    (changeOfRingsPresheaf a M ⟶ N.val) ≃
      (M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj N) where
  toFun := tensorToRestrict a M N
  invFun := tensorFromRestrict a M N
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (a.hom.app U).hom).left_inv _
  right_inv g := by
    apply hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (a.hom.app U).hom).right_inv _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def changeHomEquiv (M : SheafOfModules.{u} (𝓡 A))
    (N : SheafOfModules.{u} (𝓡 B)) :
    (changeOfRings a M ⟶ N) ≃
      (M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj N) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).homEquiv _ _).trans
    (tensorHomEquiv a M N)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem changeHomEquiv_apply (M : SheafOfModules.{u} (𝓡 A))
    (N : SheafOfModules.{u} (𝓡 B)) (h : changeOfRings a M ⟶ N)
    (U : Cᵒᵖ) (m : M.val.obj U) :
    (changeHomEquiv a M N h).val.app U m = h.val.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
        (changeOfRingsPresheaf a M)).app U
          ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] m)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem changeHomEquiv_naturality_right
    (M : SheafOfModules.{u} (𝓡 A)) (N N' : SheafOfModules.{u} (𝓡 B))
    (k : N ⟶ N') (h : changeOfRings a M ⟶ N) :
    changeHomEquiv a M N' (h ≫ k) = changeHomEquiv a M N h ≫
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).map k := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem changeHomEquiv_naturality_left
    (M M' : SheafOfModules.{u} (𝓡 A)) (N : SheafOfModules.{u} (𝓡 B))
    (k : M ⟶ M') (h : changeOfRings a M' ⟶ N) :
    changeHomEquiv a M N (changeOfRingsHom a M k ≫ h) =
      k ≫ changeHomEquiv a M' N h := by
  apply hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  rw [changeHomEquiv_apply]
  change h.val.app U ((changeOfRingsHom a M k).val.app U _) =
    (changeHomEquiv a M' N h).val.app U (k.val.app U m)
  rw [changeHomEquiv_apply]
  congr 1
  let t : changeOfRingsPresheaf a M ⟶ changeOfRingsPresheaf a M' :=
    { app U := (ModuleCat.extendScalars (a.hom.app U).hom).map (k.val.app U)
      naturality := changeOfRingsHom_naturality a M k }
  have hn := (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.naturality t
  have hx := congrArg (fun z ↦ z.app U
    ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] m)) hn
  change (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
    (changeOfRingsPresheaf a M')).app U
      ((ModuleCat.extendScalars (a.hom.app U).hom).map (k.val.app U)
        ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] m))) = _ at hx
  erw [ModuleCat.ExtendScalars.map_tmul] at hx
  exact hx.symm

end SheafOfModules

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The two AsSmall transports retain sections and linear maps literally.
private noncomputable def fromModelHomEquiv
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1})
    (P : SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A))
    (N : SheafOfModules.{u + 1} A) :
    ((proEtaleModuleFromModel A).obj P ⟶ N) ≃
      (P ⟶ (proEtaleModuleToModel A).obj N) where
  toFun h :=
    { val :=
      { app W := h.val.app (AsSmall.down.op.obj W)
        naturality := by
          intro U V i
          exact h.val.naturality (AsSmall.down.op.map i) } }
  invFun g :=
    { val :=
      { app W := g.val.app (AsSmall.up.op.obj W)
        naturality := by
          intro U V i
          exact g.val.naturality (AsSmall.up.op.map i) } }
  left_inv h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  right_inv g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def directImageModelHomEquiv
    (M : proEtaleRingModules Y R) (N : proEtaleRingModules X S) :
    ((proEtaleModuleToModel ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M ⟶
      (SheafOfModules.pushforward (proEtaleModelRingUnit f R)).obj
        ((proEtaleModuleToModel ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))).obj
          ((SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).obj N))) ≃
    (M ⟶ (proEtaleRingModuleDirectImage f R S c).obj N) where
  toFun h :=
    { val :=
      { app W := h.val.app (AsSmall.up.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply h.val (AsSmall.up.op.map i) m } }
  invFun g :=
    { val :=
      { app W := g.val.app (AsSmall.down.op.obj W)
        naturality := by
          intro U V i
          ext m
          exact PresheafOfModules.naturality_apply g.val (AsSmall.down.op.map i) m } }
  left_inv h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl
  right_inv g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def canonicalHomEquiv
    (M : proEtaleRingModules Y R) (N : proEtaleRingModules X S) :
    ((proEtaleRingModulePullback f R S c).obj M ⟶ N) ≃
      (M ⟶ (proEtaleRingModuleDirectImage f R S c).obj N) :=
  (SheafOfModules.changeHomEquiv c.hom ((proEtaleModuleInverseImage f R).obj M) N).trans
    ((fromModelHomEquiv _ _ _).trans
      (((SheafOfModules.pullbackPushforwardAdjunction
        (proEtaleModelRingUnit f R)).homEquiv _ _).trans
          (directImageModelHomEquiv f R S c M N)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem canonicalHomEquiv_naturality_left
    (M M' : proEtaleRingModules Y R) (N : proEtaleRingModules X S)
    (k : M ⟶ M') (h : (proEtaleRingModulePullback f R S c).obj M' ⟶ N) :
    canonicalHomEquiv f R S c M N ((proEtaleRingModulePullback f R S c).map k ≫ h) =
      k ≫ canonicalHomEquiv f R S c M' N h := by
  let e := (SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R))
  let t := SheafOfModules.changeHomEquiv c.hom ((proEtaleModuleInverseImage f R).obj M') N h
  have ht := SheafOfModules.changeHomEquiv_naturality_left c.hom
    ((proEtaleModuleInverseImage f R).obj M)
    ((proEtaleModuleInverseImage f R).obj M') N ((proEtaleModuleInverseImage f R).map k) h
  have hc := congrArg (fun z ↦ directImageModelHomEquiv f R S c M N
    (e.homEquiv _ _ (fromModelHomEquiv _ _ _ z))) ht
  refine hc.trans ?_
  change directImageModelHomEquiv f R S c M N
    (e.homEquiv _ _ ((SheafOfModules.pullback (proEtaleModelRingUnit f R)).map
      ((proEtaleModuleToModel _).map k) ≫ fromModelHomEquiv _ _ _ t)) =
    directImageModelHomEquiv f R S c M N
      ((proEtaleModuleToModel _).map k ≫ e.homEquiv _ _ (fromModelHomEquiv _ _ _ t))
  exact congrArg (directImageModelHomEquiv f R S c M N)
    (e.homEquiv_naturality_left ((proEtaleModuleToModel _).map k) _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem canonicalHomEquiv_naturality_right
    (M : proEtaleRingModules Y R) (N N' : proEtaleRingModules X S)
    (k : N ⟶ N') (h : (proEtaleRingModulePullback f R S c).obj M ⟶ N) :
    canonicalHomEquiv f R S c M N' (h ≫ k) =
      canonicalHomEquiv f R S c M N h ≫ (proEtaleRingModuleDirectImage f R S c).map k := by
  let e := (SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R))
  let t := SheafOfModules.changeHomEquiv c.hom ((proEtaleModuleInverseImage f R).obj M) N h
  have ht := SheafOfModules.changeHomEquiv_naturality_right c.hom
    ((proEtaleModuleInverseImage f R).obj M) N N' k h
  have hc := congrArg (fun z ↦ directImageModelHomEquiv f R S c M N'
    (e.homEquiv _ _ (fromModelHomEquiv _ _ _ z))) ht
  refine hc.trans ?_
  have hn := e.homEquiv_naturality_right (fromModelHomEquiv _ _ _ t)
    ((proEtaleModuleToModel _).map ((SheafOfModules.restrictScalars _).map k))
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext m
  exact congrArg (fun z ↦ z.val.app (AsSmall.up.op.obj W) m) hn

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical derived adjunction is induced from the normalized module adjunction. -/
noncomputable def proEtaleRingDerivedAdjunction :
    proEtaleRingDerivedPullback f R S c ⊣ proEtaleRingDerivedDirectImage f R S c :=
  (proEtaleRingModuleAdjunction f R S c).mapDerivedCategoryRightDerivedAdjunction

end AlgebraicGeometry.Scheme
