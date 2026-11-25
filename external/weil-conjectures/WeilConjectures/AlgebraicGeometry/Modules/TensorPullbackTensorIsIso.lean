/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-!
# Invertibility of the tensor-pullback comparison

## References

* Stacks Project, Modules, Tag 01CD
* Sheaves, Tag 0098
* Stacks Project, Tag 01CB
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The stalk tensor transports involve several nested sheaf and scalar-change functors.
/-- A comparison carrying pulled-back pure tensors to tensors of pulled-back sections
is an isomorphism. No naturality of the comparison is assumed. -/
theorem isIso_tensorPullback_of_tmul {X Y : Scheme.{v}} (f : X ⟶ Y)
    (M N : Y.Modules)
    (α : (tensorPullback f).obj (M ⊗ N) ⟶
      (tensorPullback f).obj M ⊗ (tensorPullback f).obj N)
    (hα : ∀ (V : Y.Opens) (s : Γ(M, V)) (t : Γ(N, V)),
      α.app (f ⁻¹ᵁ V)
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app (M ⊗ N)).val.app
            (op V) (tmulSection s t) : Γ((tensorPullback f).obj (M ⊗ N), f ⁻¹ᵁ V)) =
        tmulSection
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).val.app
            (op V) s : Γ((tensorPullback f).obj M, f ⁻¹ᵁ V))
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app N).val.app
            (op V) t : Γ((tensorPullback f).obj N, f ⁻¹ᵁ V))) : IsIso α := by
  classical
  have hstalk (x : X) : IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map α) := by
    let SX : X.Modules ⥤ ModuleCat (X.presheaf.stalk x) :=
      RingedSpace.moduleStalkFunctor X.toRingedSpace x
    let SY : Y.Modules ⥤ ModuleCat (Y.presheaf.stalk (f x)) :=
      RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x)
    let F := ModuleCat.extendScalars (f.stalkMap x).hom
    obtain ⟨p, hp⟩ := exists_tensorPullback_stalk_iso f x
    obtain ⟨tx, htx, _⟩ := SheafOfModules.stalkTensorIso X.toRingedSpace x
    obtain ⟨ty, hty, _⟩ := SheafOfModules.stalkTensorIso Y.toRingedSpace (f x)
    let l : SX.obj ((tensorPullback f).obj (M ⊗ N)) ≅ F.obj (SY.obj M ⊗ SY.obj N) :=
      p.app (M ⊗ N) ≪≫ F.mapIso (ty M N)
    let r : SX.obj ((tensorPullback f).obj M ⊗ (tensorPullback f).obj N) ≅
        F.obj (SY.obj M) ⊗ F.obj (SY.obj N) :=
      tx ((tensorPullback f).obj M) ((tensorPullback f).obj N) ≪≫
        (p.app M ⊗ᵢ p.app N)
    have he : l.inv ≫ SX.map α ≫ r.hom = (Functor.Monoidal.μIso F (SY.obj M) (SY.obj N)).inv := by
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
    have hi : IsIso (l.inv ≫ SX.map α ≫ r.hom) := by rw [he]; infer_instance
    have : IsIso (SX.map α) := by
      have hh : SX.map α = l.hom ≫ (l.inv ≫ SX.map α ≫ r.hom) ≫ r.inv := by simp
      rw [hh]
      infer_instance
    exact this
  let P : X.Modules := (tensorPullback f).obj (M ⊗ N)
  let Q : X.Modules := (tensorPullback f).obj M ⊗ (tensorPullback f).obj N
  let a : (SheafOfModules.toSheaf X.ringCatSheaf).obj P ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj Q :=
    (SheafOfModules.toSheaf X.ringCatSheaf).map α
  have hi (x : X) : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x).map a.hom) := by
    let := hstalk x
    exact (forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat).map_isIso
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map α)
  let := hi
  have := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso a
  have h : IsIso ((toPresheaf X).map α) :=
    (TopCat.Sheaf.forget AddCommGrpCat X.toTopCat).map_isIso a
  exact isIso_of_reflects_iso α (toPresheaf X)

end AlgebraicGeometry.Scheme.Modules
