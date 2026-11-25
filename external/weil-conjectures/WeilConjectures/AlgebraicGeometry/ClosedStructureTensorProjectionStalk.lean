/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks

/-! # The local calculation for the closed structure tensor projection
Source: Stacks Project, Tags 08KS, 01CB and 0098.
(blueprint: new-closed-structure-tensor-projection-stalk). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry
open Scheme.Modules

-- The unit-stalk calculation follows ClosedImmersionUnitStalkKernel.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem projection_unit_stalk_iso (X : Scheme.{u}) (x : X) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    ∃ e : S.obj (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r :=
  open CategoryTheory.Limits in by
    let D := (TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf
    let A := forget₂ CommRingCat.{u} RingCat.{u} ⋙
      forget₂ RingCat.{u} AddCommGrpCat.{u}
    let e : ↑(TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf x) ≃+ X.presheaf.stalk x :=
      (preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
    have hg (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
        e (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r := by
      change (colimit.ι (D ⋙ A) (Opposite.op (⟨U, hx⟩ : TopologicalSpace.OpenNhds x)) ≫
        (preservesColimitIso A D).inv) r = _
      rw [ι_preservesColimitIso_inv]
      rfl
    let f : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        (SheafOfModules.unit X.ringCatSheaf) →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
      { e.toAddMonoidHom with
        map_smul' := by
          intro r m
          obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
          obtain ⟨V, hxV, m, rfl⟩ :=
            TopCat.Presheaf.exists_germ_eq
              (SheafOfModules.unit X.ringCatSheaf).val.presheaf m
          have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
          rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx r,
            ← TopCat.Presheaf.germ_res_apply
              (SheafOfModules.unit X.ringCatSheaf).val.presheaf
              (homOfLE inf_le_right) x hx m,
            ← PresheafOfModules.germ_smul (R := X.presheaf)]
          let r' := X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op r
          let m' : Γ(X, U ⊓ V) :=
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf.map
              (homOfLE inf_le_right : U ⊓ V ⟶ V).op m
          change e (TopCat.Presheaf.germ
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx (r' * m')) =
            X.presheaf.germ (U ⊓ V) x hx r' * (e (TopCat.Presheaf.germ
              (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx m') :
                X.presheaf.stalk x)
          rw [hg, hg]
          exact map_mul (X.presheaf.germ (U ⊓ V) x hx).hom _ _ }
    refine ⟨(LinearEquiv.ofBijective f e.bijective).toModuleIso, ?_⟩
    exact hg

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk of a module map with the specified section-pairing formula is invertible.
Source: Stacks Project, Tags 08KS, 01CB, 0098, and Sheaves Tag 007T.
(blueprint: new-closed-structure-tensor-projection-stalk).

Proof: At a point i(z), the tensor-stalk comparison identifies the source with
M_i(z) tensor over O_Y,i(z) O_Z,z. The closed-pushforward and tensor-pullback
comparisons identify the target with O_Z,z tensor over O_Y,i(z) M_i(z).
The canonical pullback unit has germ 1 tensor m. Taking germs in the given
section formula therefore sends m tensor r to r tensor m. Represent the two
germs on a common neighbourhood, using the closed-embedding cofinality for r;
pure tensors generate, so the stalk map is scalar-extension symmetry and is
bijective. At a point outside the closed image, both pushforward stalks vanish:
restrict to the open complement. Tensor-stalk comparison makes the source
zero as well. The unique map between zero abelian groups is invertible.
The identity immersion gives tensor symmetry followed by the scalar unitor;
the empty source and the zero module give the zero-group case. -/
theorem closedStructure_projection_stalk_isIso
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (M : Y.Modules)
    (α : M ⊗ (pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (pushforward i).obj ((tensorPullback i).obj M))
    (hα : ∀ (U : Y.Opens) (s : Γ(M, U))
      (r : Γ((pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf), U)),
      α.app U (tmulSection s r) = (show Γ(Z, i ⁻¹ᵁ U) from r) •
        (show Γ((tensorPullback i).obj M, i ⁻¹ᵁ U) from
          ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app M).app U s))
    (x : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α.mapPresheaf) := by
    classical
    let B := (pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let P := (tensorPullback i).obj M
    let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace x
    obtain ⟨Φ, hΦ, _⟩ := SheafOfModules.stalkTensorIso Y.toRingedSpace x
    have hΦg (U : Y.Opens) (hx : x ∈ U) (s : Γ(M, U)) (r : Γ(B, U)) :
        (Φ M B).hom (TopCat.Presheaf.germ (M ⊗ B).val.presheaf U x hx
          (tmulSection s r)) =
        (TopCat.Presheaf.germ M.val.presheaf U x hx s) ⊗ₜ[Y.presheaf.stalk x]
          (TopCat.Presheaf.germ B.val.presheaf U x hx r) := by
      exact hΦ M B U hx s r
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      -- Identify both sides with the two orders of the scalar-extension tensor.
      obtain ⟨δ, hδ⟩ := exists_tensorPullback_stalk_iso i z
      obtain ⟨e, he⟩ := projection_unit_stalk_iso Z z
      let cB := TopCat.Presheaf.stalkPushforward Ab i.base
        (SheafOfModules.unit Z.ringCatSheaf).val.presheaf z
      let cP := TopCat.Presheaf.stalkPushforward Ab i.base P.val.presheaf z
      have hcB : IsIso cB :=
        (closedImmersion_pushforward_stalks i i.isClosedEmbedding
          (SheafOfModules.unit Z.ringCatSheaf)).2.1 z |>.2.1
      have hcP : IsIso cP :=
        (closedImmersion_pushforward_stalks i i.isClosedEmbedding P).2.1 z |>.2.1
      let ε : S.obj ((pushforward i).obj P) ≃+
          (ModuleCat.extendScalars (i.stalkMap z).hom).obj (S.obj M) :=
        (asIso cP).addCommGroupIsoToAddEquiv.trans (δ.app M).toLinearEquiv.toAddEquiv
      let b : S.obj B ≃+ Z.presheaf.stalk z :=
        (asIso cB).addCommGroupIsoToAddEquiv.trans e.toLinearEquiv.toAddEquiv
      let f := (i.stalkMap z).hom
      let T := (ModuleCat.restrictScalars f).obj
        (ModuleCat.of (Z.presheaf.stalk z) (Z.presheaf.stalk z))
      let bl : S.obj B →ₗ[Y.presheaf.stalk (i.base z)] T :=
        { b.toAddMonoidHom with
          map_smul' := by
            intro a r
            change e.hom (cB (a • r)) = f a • e.hom (cB r)
            rw [(closedImmersion_pushforward_stalks i i.isClosedEmbedding
              (SheafOfModules.unit Z.ringCatSheaf)).2.1 z |>.2.2]
            exact e.hom.hom.map_smul _ _ }
      let β : S.obj B ≃ₗ[Y.presheaf.stalk (i.base z)] T :=
        LinearEquiv.ofBijective bl b.bijective
      let q : (TensorProduct (Y.presheaf.stalk (i.base z)) (S.obj M) (S.obj B)) ≃+
          (ModuleCat.extendScalars f).obj (S.obj M) :=
        ((TensorProduct.congr (LinearEquiv.refl _ _) β).trans
          (TensorProduct.comm _ _ _)).toAddEquiv
      let a := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (i.base z)).map
        α.mapPresheaf
      have hbg (U : Y.Opens) (hz : i.base z ∈ U) (r : Γ(B, U)) :
          b (TopCat.Presheaf.germ B.val.presheaf U (i.base z) hz r) =
            Z.presheaf.germ (i ⁻¹ᵁ U) z hz (show Γ(Z, i ⁻¹ᵁ U) from r) := by
        change e.hom (cB (TopCat.Presheaf.germ B.val.presheaf U (i.base z) hz r)) = _
        erw [TopCat.Presheaf.stalkPushforward_germ_apply]
        exact he (i ⁻¹ᵁ U) hz r
      -- The section formula becomes symmetry on every pure tensor germ.
      have hg (U : Y.Opens) (hz : i.base z ∈ U) (s : Γ(M, U)) (r : Γ(B, U)) :
          ε (a (TopCat.Presheaf.germ (M ⊗ B).val.presheaf U (i.base z) hz
            (tmulSection s r))) =
          q ((TopCat.Presheaf.germ M.val.presheaf U (i.base z) hz s) ⊗ₜ[_]
            (TopCat.Presheaf.germ B.val.presheaf U (i.base z) hz r)) := by
        change (δ.hom.app M) (cP (a _)) = _
        have ham := TopCat.Presheaf.stalkFunctor_map_germ_apply U (i.base z) hz
          α.mapPresheaf (tmulSection s r)
        change a _ = _ at ham
        erw [ham]
        change (δ.hom.app M) (cP (TopCat.Presheaf.germ
          ((pushforward i).obj P).val.presheaf U (i.base z) hz
          (α.app U (tmulSection s r)))) = _
        rw [hα]
        erw [TopCat.Presheaf.stalkPushforward_germ_apply]
        erw [PresheafOfModules.germ_smul P.val]
        rw [(δ.hom.app M).hom.map_smul]
        have hd := congrArg
          (fun t : (ModuleCat.extendScalars f).obj (S.obj M) ↦
            (Z.presheaf.germ (i ⁻¹ᵁ U) z hz (show Γ(Z, i ⁻¹ᵁ U) from r)) • t)
          (hδ M U hz s)
        apply hd.trans
        change _ = (show T from b (TopCat.Presheaf.germ B.val.presheaf U (i.base z) hz r))
          ⊗ₜ[Y.presheaf.stalk (i.base z)]
            (TopCat.Presheaf.germ M.val.presheaf U (i.base z) hz s)
        rw [hbg]
        exact ModuleCat.ExtendScalars.smul_tmul f _ _ _ |>.trans (by rw [mul_one])
      let v : (TensorProduct (Y.presheaf.stalk (i.base z)) (S.obj M) (S.obj B)) →+
          (ModuleCat.extendScalars f).obj (S.obj M) :=
        ε.toAddMonoidHom.comp
          ((ConcreteCategory.hom a).comp (Φ M B).symm.toLinearEquiv.toAddMonoidHom)
      -- Every pair of stalk elements has representatives on one common neighbourhood.
      have hv (t : TensorProduct (Y.presheaf.stalk (i.base z)) (S.obj M) (S.obj B)) :
          v t = q t := by
        induction t using TensorProduct.inductionOn with
        | add t t' ht ht' => simp only [map_add, ht, ht']
        | tmul m r =>
          obtain ⟨U, hzU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
          obtain ⟨V, hzV, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq B.val.presheaf r
          have hz : i.base z ∈ U ⊓ V := ⟨hzU, hzV⟩
          rw [← TopCat.Presheaf.germ_res_apply M.val.presheaf
            (homOfLE inf_le_left : U ⊓ V ⟶ U) (i.base z) hz m,
            ← TopCat.Presheaf.germ_res_apply B.val.presheaf
            (homOfLE inf_le_right : U ⊓ V ⟶ V) (i.base z) hz r]
          let m' := M.val.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op m
          let r' := B.val.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op r
          have hinv : (Φ M B).inv
              ((TopCat.Presheaf.germ M.val.presheaf (U ⊓ V) (i.base z) hz m') ⊗ₜ[_]
                (TopCat.Presheaf.germ B.val.presheaf (U ⊓ V) (i.base z) hz r')) =
              TopCat.Presheaf.germ (M ⊗ B).val.presheaf (U ⊓ V) (i.base z) hz
                (tmulSection m' r') := by
            rw [← hΦg (U ⊓ V) hz m' r']
            exact (Φ M B).toLinearEquiv.symm_apply_apply _
          change ε (a ((Φ M B).inv _)) = _
          rw [hinv]
          exact hg (U ⊓ V) hz m' r'
      have ha : Function.Bijective a := by
        have heq (t : S.obj (tensorObj M B)) :
            ε (a t) = q ((Φ M B).hom t) := by
          have hh := hv ((Φ M B).hom t)
          change ε (a ((Φ M B).inv ((Φ M B).hom t))) = _ at hh
          simpa only [ModuleCat.inv_hom_apply] using hh
        constructor
        · intro t t' htt'
          apply (Φ M B).toLinearEquiv.injective
          apply q.injective
          change q ((Φ M B).hom t) = q ((Φ M B).hom t')
          exact (heq t).symm.trans ((congrArg ε htt').trans (heq t'))
        · intro t
          obtain ⟨w, hw⟩ := q.surjective (ε t)
          refine ⟨(Φ M B).inv w, ε.injective ?_⟩
          rw [heq]
          simpa only [ModuleCat.hom_inv_apply] using hw
      exact (ConcreteCategory.isIso_iff_bijective a).mpr ha
    · have hB := (closedImmersion_pushforward_stalks i i.isClosedEmbedding
        (SheafOfModules.unit Z.ringCatSheaf)).1 x hx
      have hP := (closedImmersion_pushforward_stalks i i.isClosedEmbedding P).1 x hx
      have hBModule : Subsingleton
          ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).obj B) := hB
      have hTensor : Subsingleton
          (TensorProduct (Y.presheaf.stalk x)
            ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).obj M)
            ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).obj B)) := inferInstance
      have hs : Subsingleton (S.obj (tensorObj M B)) :=
        (Φ M B).toLinearEquiv.injective.subsingleton
      have hs' : Subsingleton (TopCat.Presheaf.stalk (C := Ab.{u})
          (X := Y.toTopCat) (M ⊗ B).val.presheaf x) := hs
      have hP' : Subsingleton
          (TopCat.Presheaf.stalk (C := Ab.{u}) (X := Y.toTopCat)
            ((pushforward i).obj P).val.presheaf x) := hP
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      constructor
      · intro a b h
        exact hs'.elim _ _
      · intro a
        exact ⟨0, hP'.elim _ _⟩

end AlgebraicGeometry
