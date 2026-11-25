/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
import Mathlib.CategoryTheory.Sites.Adjunction

/-! # The normalized unit after forgetting fixed scalars -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

private abbrev Fgt (l : ℕ) [Fact l.Prime] :=
  ModuleCat.restrictScalars (Int.castRingHom (ULift.{u + 1} ℤ_[l])) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}

private theorem Fgt_leftAdjoint (l : ℕ) [Fact l.Prime] : (Fgt.{u} l).IsLeftAdjoint := by
  exact ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, u + 1}
    (Int.castRingHom (ULift.{u + 1} ℤ_[l]))).comp
      (forget₂ (ModuleCat.{u + 1} ℤ)
        AddCommGrpCat.{u + 1}).asEquivalence.toAdjunction).isLeftAdjoint

attribute [local instance] Fgt_leftAdjoint

private def forgetPullbackIso (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f ⋙ diagonalForget l X ≅
      diagonalForget l S ⋙ upperStar AddCommGrpCat.{u + 1} f := by
  let J := Scheme.ProEt.topology S
  let K := Scheme.ProEt.topology X
  let F := Scheme.proEtaleBaseChange f
  let U := Fgt.{u} l
  let E := ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])
  let D := AddCommGrpCat.{u + 1}
  exact NatIso.ofComponents (fun A ↦
    ((sheafComposeNatIso K U (sheafificationAdjunction K E)
      (sheafificationAdjunction K D)).app (F.op.lan.obj A.obj)).symm ≪≫
    (presheafToSheaf K D).mapIso
      ((U.lanCompIsoOfPreserves F.op).app A.obj))
    (by
      intro A B g
      change (presheafToSheaf K E ⋙ sheafCompose K U).map (F.op.lan.map g.hom) ≫
          (sheafComposeNatIso K U (sheafificationAdjunction K E)
            (sheafificationAdjunction K D)).inv.app _ ≫ _ = _
      rw [(sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K D)).inv.naturality_assoc]
      change _ ≫ (presheafToSheaf K D).map _ ≫ (presheafToSheaf K D).map _ =
        _ ≫ (presheafToSheaf K D).map _ ≫ (presheafToSheaf K D).map _
      simp only [← CategoryTheory.Functor.map_comp]
      congr 2
      exact (U.lanCompIsoOfPreserves F.op).hom.naturality g.hom)

private theorem forgetPullbackIso_unit (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : DiagonalMod l S) :
    (diagonalForget l S).map
        ((upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).unit.app M) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map ((forgetPullbackIso l f).hom.app M) =
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
      ((diagonalForget l S).obj M) := by
  let J := Scheme.ProEt.topology S
  let K := Scheme.ProEt.topology X
  let F := Scheme.proEtaleBaseChange f
  let U := Fgt.{u} l
  let E := ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])
  let D := AddCommGrpCat.{u + 1}
  apply (sheafToPresheaf J D).map_injective
  change Functor.whiskerRight ((sheafToPresheaf J E).map
      ((sheafAdjunctionContinuous F E J K).unit.app M)) U ≫ _ = _
  simp only [sheafAdjunctionContinuous, sheafPullback,
    Adjunction.map_restrictFullyFaithful_unit_app]
  dsimp only [Functor.comp_obj, Functor.id_obj, Iso.refl_hom, NatTrans.id_app]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [Adjunction.comp_unit_app, Functor.comp_obj, Category.comp_id]
  change Functor.whiskerRight ((F.op.lanAdjunction E).unit.app M.obj ≫
      Functor.whiskerLeft F.op ((sheafificationAdjunction K E).unit.app _)) U ≫
      Functor.whiskerLeft F.op
        (((sheafComposeNatIso K U (sheafificationAdjunction K E)
          (sheafificationAdjunction K D)).inv.app _).hom ≫
        ((presheafToSheaf K D).map
          ((U.lanCompIsoOfPreserves F.op).hom.app M.obj)).hom) =
    (F.op.lanAdjunction D).unit.app (M.obj ⋙ U) ≫
      Functor.whiskerLeft F.op ((sheafificationAdjunction K D).unit.app _)
  simp only [Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  have hs : Functor.whiskerRight
      ((sheafificationAdjunction K E).unit.app (F.op.lan.obj M.obj)) U ≫
      ((sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K D)).inv.app _).hom =
      (sheafificationAdjunction K D).unit.app (F.op.lan.obj M.obj ⋙ U) := by
    have h := sheafComposeNatTrans_fac K U (sheafificationAdjunction K E)
      (sheafificationAdjunction K D) (F.op.lan.obj M.obj)
    rw [← h]
    simp only [Category.assoc]
    change _ ≫ ((sheafToPresheaf K D).map
      ((sheafComposeNatIso K U (sheafificationAdjunction K E)
        (sheafificationAdjunction K D)).hom.app _) ≫
      (sheafToPresheaf K D).map _) = _
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
    simp
  have hn := (sheafificationAdjunction K D).unit.naturality
    ((U.lanCompIsoOfPreserves F.op).hom.app M.obj)
  have hk := U.leftKanExtensionCompIsoOfPreserves_hom_fac M.obj F.op
  ext V x
  have hs' := congrArg (fun t ↦ t.app (F.op.obj V)) hs
  have hn' := congrArg (fun t ↦ t.app (F.op.obj V)) hn
  have hk' := congrArg (fun t ↦ t.app V) hk
  simp only [Functor.lanAdjunction_unit] at hs' hn' hk' ⊢
  dsimp [Functor.lanCompIsoOfPreserves, Functor.lanUnit] at hs' hn' hk' ⊢
  simp only [Category.id_comp] at hk'
  have hsx := ConcreteCategory.congr_hom hs'
    ((U.map ((F.op.leftKanExtensionUnit M.obj).app V)) x)
  have hnx := ConcreteCategory.congr_hom hn'
    ((U.map ((F.op.leftKanExtensionUnit M.obj).app V)) x)
  have hkx := ConcreteCategory.congr_hom hk' x
  dsimp at hsx hnx hkx
  exact (congrArg (fun y ↦ (((presheafToSheaf K D).map
      (U.leftKanExtensionCompIsoOfPreserves M.obj F.op).hom).hom.app (F.op.obj V)) y)
    hsx).trans (hnx.symm.trans (congrArg (fun y ↦
      ((toSheafify K (F.op.leftKanExtension (M.obj ⋙ U))).app (F.op.obj V)) y) hkx))

/-- Forgetting constant scalars carries the actual inverse-image unit to an
invertible abelian inverse-image adjunct.

Source: Stacks Project, Modules on Sites, Tag 03D3.
The scalar forgetful functor is left adjoint to coinduction, so it preserves
left Kan extensions and sheafification. The two canonical comparisons give
an isomorphism commuting with the inverse-image units: expand the units,
use the sheafification unit equation, naturality, and the left Kan extension
unit equation. Under the abelian adjunction its inverse is precisely the
adjunct asserted here, which is therefore invertible.
(blueprint: new-sfb-diagonal-rlim-forget-unit). -/
theorem diagonalRlimForgetUnit (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (M : DiagonalMod l S) :
    IsIso (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
      ((diagonalForget l S).obj M)
      ((diagonalForget l X).obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).obj M))).symm
      ((diagonalForget l S).map
        ((upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).unit.app M))) := by
  let a := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let e := forgetPullbackIso l f
  have he : (a.homEquiv ((diagonalForget l S).obj M)
      ((diagonalForget l X).obj
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).obj M))).symm
      ((diagonalForget l S).map
        ((upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).unit.app M)) = e.inv.app M := by
    apply (a.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    apply (cancel_mono ((lowerStar AddCommGrpCat.{u + 1} f).map (e.hom.app M))).1
    rw [forgetPullbackIso_unit l f M]
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [he]
  infer_instance

end AlgebraicGeometry.ProEtale.DiagonalTrace
