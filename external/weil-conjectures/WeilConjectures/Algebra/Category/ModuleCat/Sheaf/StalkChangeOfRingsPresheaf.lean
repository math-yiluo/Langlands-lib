/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Stalks of sectionwise extension of scalars

Source: Stacks Project, Sheaves, Lemma 007K (blueprint:
lem-weil-pbc-presheaf-stalk-change-of-rings-tensor).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf
open scoped ChangeOfRings

namespace SheafOfModules

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance localInst_StalkChangeOfRingsPresheaf_1 {X : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    Module (R.obj.obj V)
      ((ModuleCat.restrictScalars (((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj.map f).hom).obj (F.val.obj V)) :=
  inferInstanceAs (Module (R.obj.obj V) (F.val.obj V))

private theorem changeOfRingsMap_tmul' {X : TopCat.{u}}
    {R₁ R₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (α : R₁ ⟶ R₂)
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁))
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (a : R₂.obj.obj U) (s : F.val.obj U) :
    changeOfRingsMap α F f (a ⊗ₜ[R₁.obj.obj U, (α.hom.app U).hom] s) =
      R₂.obj.map f a ⊗ₜ[R₁.obj.obj V, (α.hom.app V).hom] F.val.map f s := by
  exact Classical.choose_spec (exists_changeOfRingsMap α F f) a s

-- The section map s ↦ 1 ⊗ s induces a stalk map; extend scalars to obtain ψ.
private theorem exists_stalkChangeOfRingsMap (X : TopCat.{u})
    (R₁ R₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (α : R₁ ⟶ R₂) (x : X)
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁)) :
    ∃ ψ : (ModuleCat.extendScalars ((stalkFunctor CommRingCat x).map α.hom).hom).obj
        (ModuleCat.of (stalk (C := CommRingCat.{u}) R₁.obj x)
          (stalk (C := Ab.{u}) F.val.presheaf x)) ⟶
      ModuleCat.of (stalk (C := CommRingCat.{u}) R₂.obj x)
        (stalk (C := Ab.{u}) (changeOfRingsPresheaf α F).presheaf x),
      ∀ (U : Opens X) (hx : x ∈ U) (s : F.val.obj (op U)) (a : R₂.obj.obj (op U)),
        ψ (germ R₂.obj U x hx a
          ⊗ₜ[stalk (C := CommRingCat.{u}) R₁.obj x,
            ((stalkFunctor CommRingCat x).map α.hom).hom]
          germ F.val.presheaf U x hx s) =
        germ (changeOfRingsPresheaf α F).presheaf U x hx
          (a ⊗ₜ[R₁.obj.obj (op U), (α.hom.app (op U)).hom] s) := by
  let P := changeOfRingsPresheaf.{u, u, u} α F
  let t : F.val.presheaf ⟶ P.presheaf :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ (1 : R₂.obj.obj U) ⊗ₜ[R₁.obj.obj U, (α.hom.app U).hom] s
          map_zero' := by simp
          map_add' := by intros; simp [TensorProduct.tmul_add] }
      naturality := by
        intro U V f
        ext s
        change (1 : R₂.obj.obj V) ⊗ₜ[R₁.obj.obj V, (α.hom.app V).hom]
          F.val.map f s = changeOfRingsMap α F f
          ((1 : R₂.obj.obj U) ⊗ₜ[R₁.obj.obj U, (α.hom.app U).hom] s)
        erw [changeOfRingsMap_tmul']
        simp }
  let h : stalk (C := Ab.{u}) F.val.presheaf x →+
      stalk (C := Ab.{u}) P.presheaf x :=
    ConcreteCategory.hom ((stalkFunctor Ab.{u} x).map t)
  have hg (U : Opens X) (hx : x ∈ U) (s : F.val.obj (op U)) :
      h (germ F.val.presheaf U x hx s) =
        germ P.presheaf U x hx
          ((1 : R₂.obj.obj (op U)) ⊗ₜ[R₁.obj.obj (op U), (α.hom.app (op U)).hom] s) := by
    exact stalkFunctor_map_germ_apply U x hx t s
  let β : stalk (C := CommRingCat.{u}) R₁.obj x →+*
      stalk (C := CommRingCat.{u}) R₂.obj x :=
    ((stalkFunctor CommRingCat x).map α.hom).hom
  let N := ModuleCat.of (stalk (C := CommRingCat.{u}) R₂.obj x)
    (stalk (C := Ab.{u}) P.presheaf x)
  let l : ModuleCat.of (stalk (C := CommRingCat.{u}) R₁.obj x)
      (stalk (C := Ab.{u}) F.val.presheaf x) ⟶ (ModuleCat.restrictScalars β).obj N :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars β).obj N)
      { toFun := h
        map_add' := h.map_add
        map_smul' := by
          intro r m
          obtain ⟨U, hxU, r, rfl⟩ := exists_germ_eq (C := CommRingCat.{u}) R₁.obj r
          obtain ⟨V, hxV, m, rfl⟩ := exists_germ_eq F.val.presheaf m
          have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
          rw [← germ_res_apply R₁.obj (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
            ← germ_res_apply F.val.presheaf (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m]
          rw [← PresheafOfModules.germ_smul, hg]
          change _ = β (germ R₁.obj (U ⊓ V) x hx _) • h _
          rw [hg]
          erw [stalkFunctor_map_germ_apply]
          rw [← PresheafOfModules.germ_smul]
          apply congrArg (germ P.presheaf (U ⊓ V) x hx)
          let : Module (R₁.obj.obj (op (U ⊓ V))) (R₂.obj.obj (op (U ⊓ V))) :=
            Module.compHom _ (α.hom.app (op (U ⊓ V))).hom
          change (1 : R₂.obj.obj (op (U ⊓ V))) ⊗ₜ[R₁.obj.obj (op (U ⊓ V))]
            (_ • (show F.val.obj (op (U ⊓ V)) from _)) = _
          rw [TensorProduct.tmul_smul]
          rfl }
  refine ⟨ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars β l, ?_⟩
  intro U hx s a
  let : Module (stalk (C := CommRingCat.{u}) R₁.obj x)
      (stalk (C := CommRingCat.{u}) R₂.obj x) := Module.compHom _ β
  let : Module (stalk (C := CommRingCat.{u}) R₁.obj x) N := Module.compHom _ β
  erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply,
    TensorProduct.lift.tmul]
  change germ R₂.obj U x hx a • h (germ F.val.presheaf U x hx s) = _
  rw [hg, ← PresheafOfModules.germ_smul]
  apply congrArg (germ P.presheaf U x hx)
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

-- The tensor of germ maps gives a cocone and an additive left inverse.
private theorem stalkChangeOfRingsMap_injective (X : TopCat.{u})
    (R₁ R₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (α : R₁ ⟶ R₂) (x : X)
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁))
    (ψ : (ModuleCat.extendScalars ((stalkFunctor CommRingCat x).map α.hom).hom).obj
        (ModuleCat.of (stalk (C := CommRingCat.{u}) R₁.obj x)
          (stalk (C := Ab.{u}) F.val.presheaf x)) ⟶
      ModuleCat.of (stalk (C := CommRingCat.{u}) R₂.obj x)
        (stalk (C := Ab.{u}) (changeOfRingsPresheaf α F).presheaf x))
    (hψ : ∀ (U : Opens X) (hx : x ∈ U) (s : F.val.obj (op U)) (a : R₂.obj.obj (op U)),
        ψ (germ R₂.obj U x hx a
          ⊗ₜ[stalk (C := CommRingCat.{u}) R₁.obj x,((stalkFunctor CommRingCat x).map α.hom).hom]
          germ F.val.presheaf U x hx s) =
        germ (changeOfRingsPresheaf α F).presheaf U x hx
          (a ⊗ₜ[R₁.obj.obj (op U),(α.hom.app (op U)).hom] s)) : Function.Injective ψ := by
  let β : stalk (C := CommRingCat.{u}) R₁.obj x →+*
      stalk (C := CommRingCat.{u}) R₂.obj x :=
    ((stalkFunctor CommRingCat x).map α.hom).hom
  let : Module (stalk (C := CommRingCat.{u}) R₁.obj x)
      (stalk (C := CommRingCat.{u}) R₂.obj x) := Module.compHom _ β
  let P := changeOfRingsPresheaf.{u, u, u} α F
  let Z := TensorProduct (stalk (C := CommRingCat.{u}) R₁.obj x)
    (stalk (C := CommRingCat.{u}) R₂.obj x) (stalk (C := Ab.{u}) F.val.presheaf x)
  let q (U : Opens X) (hx : x ∈ U) : P.obj (op U) →+ Z := by
    let : Module (R₁.obj.obj (op U)) (R₂.obj.obj (op U)) :=
      Module.compHom _ (α.hom.app (op U)).hom
    let σ := (germ R₁.obj U x hx).hom
    let f : R₂.obj.obj (op U) →ₛₗ[σ] stalk (C := CommRingCat.{u}) R₂.obj x :=
      { toFun := germ R₂.obj U x hx
        map_add' := map_add (ConcreteCategory.hom (germ R₂.obj U x hx))
        map_smul' := by
          intro r a
          change germ R₂.obj U x hx (α.hom.app (op U) r * a) =
            β (germ R₁.obj U x hx r) * germ R₂.obj U x hx a
          rw [map_mul]
          erw [stalkFunctor_map_germ_apply] }
    let g : F.val.obj (op U) →ₛₗ[σ] stalk (C := Ab.{u}) F.val.presheaf x :=
      { toFun := germ F.val.presheaf U x hx
        map_add' := map_add (ConcreteCategory.hom (germ F.val.presheaf U x hx))
        map_smul' := fun r s ↦ PresheafOfModules.germ_smul F.val x U hx r s }
    exact (TensorProduct.map f g).toAddMonoidHom
  have hq (U : Opens X) (hx : x ∈ U) (a : R₂.obj.obj (op U))
      (s : F.val.obj (op U)) :
      q U hx (a ⊗ₜ[R₁.obj.obj (op U),(α.hom.app (op U)).hom] s) =
        germ R₂.obj U x hx a ⊗ₜ[stalk (C := CommRingCat.{u}) R₁.obj x, β]
          germ F.val.presheaf U x hx s := by
    let : Module (R₁.obj.obj (op U)) (R₂.obj.obj (op U)) :=
      Module.compHom _ (α.hom.app (op U)).hom
    exact TensorProduct.map_tmul _ _ a s
  let D := (OpenNhds.inclusion x).op ⋙ P.presheaf
  let c : CategoryTheory.Limits.Cocone D :=
    { pt := AddCommGrpCat.of Z
      ι :=
        { app := fun U ↦ AddCommGrpCat.ofHom (q U.unop.val U.unop.property)
          naturality := by
            intro U V f
            ext t
            change q V.unop.val V.unop.property (P.map ((OpenNhds.inclusion x).op.map f) t) =
              q U.unop.val U.unop.property t
            let : Module (R₁.obj.obj (op U.unop.val)) (R₂.obj.obj (op U.unop.val)) :=
              Module.compHom _ (α.hom.app (op U.unop.val)).hom
            change TensorProduct (R₁.obj.obj (op U.unop.val)) (R₂.obj.obj (op U.unop.val))
              (F.val.obj (op U.unop.val)) at t
            induction t using TensorProduct.inductionOn with
            | tmul a s =>
              erw [changeOfRingsMap_tmul']
              erw [hq, hq]
              erw [germ_res_apply', germ_res_apply']
              rfl
            | add t v ht hv => simp only [map_add, ht, hv] } }
  let Q : stalk (C := Ab.{u}) P.presheaf x →+ Z :=
    ConcreteCategory.hom (CategoryTheory.Limits.colimit.desc D c)
  have hQ (U : Opens X) (hx : x ∈ U) (t : P.obj (op U)) :
      Q (germ P.presheaf U x hx t) = q U hx t := by
    exact ConcreteCategory.congr_hom (CategoryTheory.Limits.colimit.ι_desc c (op ⟨U, hx⟩)) t
  have hleft (t : Z) : Q (ψ t) = t := by
    induction t using TensorProduct.inductionOn with
    | tmul a s =>
      obtain ⟨U, hxU, a, rfl⟩ := exists_germ_eq (C := CommRingCat.{u}) R₂.obj a
      obtain ⟨V, hxV, s, rfl⟩ := exists_germ_eq F.val.presheaf s
      have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
      rw [← germ_res_apply R₂.obj (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx a,
        ← germ_res_apply F.val.presheaf (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx s,
        hψ, hQ, hq]
    | add t v ht hv => simp only [map_add, ht, hv]
  exact Function.LeftInverse.injective hleft

/-- The stalk comparison before sheafification, with its germ formula.
Source: Stacks Project, Sheaves, Lemma 007K (lemma-stalk-tensor-presheaf-modules).
(blueprint: lem-weil-pbc-presheaf-stalk-change-of-rings-tensor).

Proof: The section maps s ↦ 1 ⊗ s define an additive presheaf morphism. Its stalk
map is semilinear along α_x: represent a scalar and vector on a common neighborhood
and use the germ scalar-action formula. The extend/restrict scalars adjunction gives
an R₂,x-linear comparison ψ with ψ(germ(a) ⊗ germ(s)) = germ(a ⊗ s).
For injectivity, tensor the two semilinear germ maps on each neighborhood. These
additive maps commute with restrictions, so the neighborhood colimit universal
property gives an additive map Q in the reverse direction. Represent both factors of
a pure stalk tensor on a common neighborhood to obtain Q(ψ(t)) = t; tensor induction
extends this to every t. For surjectivity, represent a stalk element by a section
tensor and induct on that tensor: zero, pure tensors and sums all lift through ψ.
The resulting linear equivalence gives the module isomorphism and its germ formula.
The formula determines the comparison uniquely, since pure tensors generate and
pairs of germs can be represented on a common neighborhood. -/
theorem stalkChangeOfRingsPresheafIso (X : TopCat.{u})
    (R₁ R₂ : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (α : R₁ ⟶ R₂) (x : X) :
    ∃ Φ : ∀ F : SheafOfModules.{u}
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁),
      (ModuleCat.extendScalars ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.hom).hom).obj
        (ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₁.obj x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) F.val.presheaf x)) ≅
      ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₂.obj x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X) (changeOfRingsPresheaf α F).presheaf x),
      (∀ (F : SheafOfModules.{u}
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁))
        (U : Opens X) (hx : x ∈ U) (s : F.val.obj (op U)) (a : R₂.obj.obj (op U)),
        (Φ F).hom
          (TopCat.Presheaf.germ (C := CommRingCat.{u}) (X := X) R₂.obj U x hx a
          ⊗ₜ[TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R₁.obj x,
            ((TopCat.Presheaf.stalkFunctor CommRingCat x).map α.hom).hom]
            TopCat.Presheaf.germ (C := Ab.{u}) (X := X) F.val.presheaf U x hx s) =
          TopCat.Presheaf.germ (C := Ab.{u}) (X := X) (changeOfRingsPresheaf α F).presheaf U x hx
            (a ⊗ₜ[R₁.obj.obj (op U), (α.hom.app (op U)).hom] s)) := by
  classical
  have h (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁)) :=
    exists_stalkChangeOfRingsMap X R₁ R₂ α x F
  choose ψ hψ using h
  have hs (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R₁)) : Function.Surjective (ψ F) := by
    intro m
    obtain ⟨U, hx, t, rfl⟩ := exists_germ_eq (changeOfRingsPresheaf α F).presheaf m
    change ∃ z, ψ F z = germ (changeOfRingsPresheaf α F).presheaf U x hx t
    let : Module (R₁.obj.obj (op U)) (R₂.obj.obj (op U)) :=
      Module.compHom _ (α.hom.app (op U)).hom
    change TensorProduct (R₁.obj.obj (op U)) (R₂.obj.obj (op U))
      (F.val.obj (op U)) at t
    induction t using TensorProduct.inductionOn with
    | tmul a s => exact ⟨_, hψ F U hx s a⟩
    | add t v ht hv =>
      obtain ⟨a, ha⟩ := ht
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by simp only [map_add, ha, hb]⟩
  let Φ := fun F ↦ (LinearEquiv.ofBijective (ψ F).hom
    ⟨stalkChangeOfRingsMap_injective X R₁ R₂ α x F (ψ F) (hψ F), hs F⟩).toModuleIso
  refine ⟨Φ, ?_⟩
  intro F U hx s a
  exact hψ F U hx s a

end SheafOfModules
