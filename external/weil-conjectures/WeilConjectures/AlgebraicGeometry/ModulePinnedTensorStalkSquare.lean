/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
public import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-! # The module tensor pullback square on stalks

Source: Stacks Project, Modules, Tags 01CD and 01CB; Sheaves, Tag 0098.
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped ChangeOfRings
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

-- The stalk tensor transports require elaborating nested scalar-change functors.
/-- The canonical module tensor pullback and stalk maps commute with the scalar tensorator.

Proof: use extension-of-scalars extensionality and tensor induction. Represent the two
stalk vectors by sections on a common neighborhood. The source tensor stalk map sends
its pure tensor germ to the tensor of the germs, and the pullback stalk map sends the
pulled-back germ to one tensor the original germ. The pullback tensor comparison sends
pulled-back pure tensors to tensors of pulled-back sections. Applying the target tensor
stalk map and the two pullback stalk maps therefore gives the scalar tensorator on
one tensor a pure tensor. Additivity and scalar linearity give equality everywhere.
Source: Stacks Project, Modules, Tags 01CD and 01CB; Sheaves, Tag 0098.
(blueprint: lem-pc-module-pinned-tensor-stalk-square). -/
theorem module_pinned_tensor_stalk_square {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) (M N : Y.Modules) :
    let SX := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    let SY := RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x)
    let E := ModuleCat.extendScalars.{u, u, u} (f.stalkMap x).hom
    let p := Classical.choose (exists_tensorPullback_stalk_iso f x)
    let tx := Classical.choose (SheafOfModules.stalkTensorIso X.toRingedSpace x)
    let ty := Classical.choose (SheafOfModules.stalkTensorIso Y.toRingedSpace (f x))
    let c := Classical.choose (module_pullback_tensor f)
    (Functor.Monoidal.μIso E (SY.obj M) (SY.obj N)).hom ≫
        E.map (ty M N).inv ≫ p.inv.app (M ⊗ N) ≫ SX.map (c M N).hom ≫
        (tx ((tensorPullback f).obj M) ((tensorPullback f).obj N)).hom =
      p.inv.app M ⊗ₘ p.inv.app N := by
  classical
  let SX := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let SY := RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x)
  let F := ModuleCat.extendScalars.{u, u, u} (f.stalkMap x).hom
  let p := Classical.choose (exists_tensorPullback_stalk_iso f x)
  have hp := Classical.choose_spec (exists_tensorPullback_stalk_iso f x)
  let tx := Classical.choose (SheafOfModules.stalkTensorIso X.toRingedSpace x)
  have htx := (Classical.choose_spec (SheafOfModules.stalkTensorIso X.toRingedSpace x)).1
  let ty := Classical.choose (SheafOfModules.stalkTensorIso Y.toRingedSpace (f x))
  have hty :=
    (Classical.choose_spec (SheafOfModules.stalkTensorIso Y.toRingedSpace (f x))).1
  let c := Classical.choose (module_pullback_tensor f)
  let α := (c M N).hom
  have hα := (Classical.choose_spec (module_pullback_tensor f)).2 M N
  let l := p.app (M ⊗ N) ≪≫ F.mapIso (ty M N)
  let r := tx ((tensorPullback f).obj M) ((tensorPullback f).obj N) ≪≫
    (p.app M ⊗ᵢ p.app N)
  have he : l.inv ≫ SX.map α ≫ r.hom =
      (Functor.Monoidal.μIso F (SY.obj M) (SY.obj N)).inv := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
    | tmul s t =>
      obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf s
      obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq N.val.presheaf t
      have hx : f x ∈ U ⊓ V := ⟨hxU, hxV⟩
      rw [← TopCat.Presheaf.germ_res_apply M.val.presheaf
        (homOfLE inf_le_left : U ⊓ V ⟶ U) (f x) hx s,
        ← TopCat.Presheaf.germ_res_apply N.val.presheaf
        (homOfLE inf_le_right : U ⊓ V ⟶ V) (f x) hx t]
      let s' : Γ(M, U ⊓ V) := M.presheaf.map (homOfLE inf_le_left).op s
      let t' : Γ(N, U ⊓ V) := N.presheaf.map (homOfLE inf_le_right).op t
      have hy := hty M N (U ⊓ V) hx s' t'
      change (ty M N).hom
        (TopCat.Presheaf.germ (M ⊗ N).val.presheaf (U ⊓ V) (f x) hx
          (tmulSection s' t')) = _ at hy
      have hl := hp (M ⊗ N) (U ⊓ V) hx (tmulSection s' t')
      have hh : l.hom
          (TopCat.Presheaf.germ ((tensorPullback f).obj (M ⊗ N)).val.presheaf
            (f ⁻¹ᵁ (U ⊓ V)) x hx
            (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
              (M ⊗ N)).val.app (op (U ⊓ V)) (tmulSection s' t'))) =
          (1 : X.presheaf.stalk x) ⊗ₜ[_, (f.stalkMap x).hom]
            (TensorProduct.tmul (Y.presheaf.stalk (f x)) (M := SY.obj M) (N := SY.obj N)
              (TopCat.Presheaf.germ M.val.presheaf (U ⊓ V) (f x) hx s')
              (TopCat.Presheaf.germ N.val.presheaf (U ⊓ V) (f x) hx t')) := by
        change F.map (ty M N).hom ((p.hom.app (M ⊗ N)) _) = _
        rw [hl]
        erw [ModuleCat.ExtendScalars.map_tmul]
        rw [hy]
      have hi := congrArg (fun z ↦ l.inv z) hh
      simp only [Iso.hom_inv_id_apply] at hi
      have ha := TopCat.Presheaf.stalkFunctor_map_germ_apply
        (f ⁻¹ᵁ (U ⊓ V)) x hx ((PresheafOfModules.toPresheaf _).map α.val)
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
          (M ⊗ N)).val.app (op (U ⊓ V)) (tmulSection s' t'))
      have ht := htx ((tensorPullback f).obj M) ((tensorPullback f).obj N)
        (f ⁻¹ᵁ (U ⊓ V)) hx
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).val.app
          (op (U ⊓ V)) s')
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app N).val.app
          (op (U ⊓ V)) t')
      change (tx ((tensorPullback f).obj M) ((tensorPullback f).obj N)).hom
        (TopCat.Presheaf.germ
          ((tensorPullback f).obj M ⊗ (tensorPullback f).obj N).val.presheaf
          (f ⁻¹ᵁ (U ⊓ V)) x hx (tmulSection _ _)) = _ at ht
      change r.hom (SX.map α (l.inv _)) = _
      have hz := congrArg (fun z ↦ r.hom (SX.map α z)) hi.symm
      refine hz.trans ?_
      change r.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf _).map α.val) _) = _
      refine (congrArg (fun z ↦ r.hom z) ha).trans ?_
      have hsec := hα (U ⊓ V) s' t'
      have hg := congrArg (TopCat.Presheaf.germ
        ((tensorPullback f).obj M ⊗ (tensorPullback f).obj N).val.presheaf
        (f ⁻¹ᵁ (U ⊓ V)) x hx) hsec
      change (p.hom.app M ⊗ₘ p.hom.app N)
        ((tx ((tensorPullback f).obj M) ((tensorPullback f).obj N)).hom _) = _
      refine (congrArg (fun z ↦ (p.hom.app M ⊗ₘ p.hom.app N)
        ((tx ((tensorPullback f).obj M) ((tensorPullback f).obj N)).hom z)) hg).trans ?_
      refine (congrArg (fun z ↦ (p.hom.app M ⊗ₘ p.hom.app N) z) ht).trans ?_
      refine (ModuleCat.MonoidalCategory.tensorHom_tmul _ _ _ _).trans ?_
      exact congrArg₂ (fun s t ↦ s ⊗ₜ[X.presheaf.stalk x] t)
        (hp M (U ⊓ V) hx s') (hp N (U ⊓ V) hx t')
  change (Functor.Monoidal.μIso F (SY.obj M) (SY.obj N)).hom ≫
    F.map (ty M N).inv ≫ p.inv.app (M ⊗ N) ≫ SX.map α ≫
    (tx ((tensorPullback f).obj M) ((tensorPullback f).obj N)).hom =
      p.inv.app M ⊗ₘ p.inv.app N
  apply (cancel_mono (p.hom.app M ⊗ₘ p.hom.app N)).1
  change (Functor.Monoidal.μIso F (SY.obj M) (SY.obj N)).hom ≫
    (l.inv ≫ SX.map α ≫ r.hom) =
      (p.inv.app M ⊗ₘ p.inv.app N) ≫ (p.hom.app M ⊗ₘ p.hom.app N)
  rw [he, Iso.hom_inv_id, tensorHom_comp_tensorHom, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app, tensorHom_id, id_whiskerRight]
  rfl

end AlgebraicGeometry.Scheme.Modules
