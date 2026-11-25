/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.TildeScalarSectionAction
import WeilConjectures.AlgebraicGeometry.QuasicoherentSheafHom
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.InternalHomOverEquiv
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomOver

/-! # Affine dual and restriction

## References

* Stacks Project, Tag 0583, as used in Tag 0EY6, proof of (1)
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

open Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Send a module functional to the global section of the sheaf internal Hom defined
by its associated-sheaf morphism. -/
private noncomputable def affineDualGlobalSection (A : CommRingCat.{u}) (M : ModuleCat.{u} A)
    (φ : Module.Dual A M) :
    (SheafOfModules.homObj (R := (Spec A).sheaf) (tilde M)
      (SheafOfModules.unit (Spec A).ringCatSheaf)).sections :=
  (SheafOfModules.homObjSectionsEquiv.{u, u, u, u} (R := (Spec A).sheaf)
    (tilde M) (SheafOfModules.unit (Spec A).ringCatSheaf)).symm
    (tilde.map (R := A) (ModuleCat.ofHom (X := M) (Y := ModuleCat.of A A) φ) ≫
      tildeSelf.{u}.hom)

open Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical evaluation map on global sections of the affine dual. -/
private noncomputable def affineDualGlobalSectionLinear
    (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    Module.Dual A M →ₗ[A]
      Γ(SheafOfModules.homObj (R := (Spec A).sheaf) (tilde M)
        (SheafOfModules.unit (Spec A).ringCatSheaf), ⊤) where
  toFun φ := (affineDualGlobalSection A M φ).val (op ⊤)
  map_add' φ ψ := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change (tilde.map (R := A) (ModuleCat.ofHom (φ + ψ))).app U.unop.left x =
      (tilde.map (R := A) (ModuleCat.ofHom φ)).app U.unop.left x +
        (tilde.map (R := A) (ModuleCat.ofHom ψ)).app U.unop.left x
    rw [show ModuleCat.ofHom (φ + ψ) = ModuleCat.ofHom φ + ModuleCat.ofHom ψ from rfl,
      tilde.map_add]
    rfl
  map_smul' r φ := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    change (tilde.map (R := A) (ModuleCat.ofHom (r • φ))).app U.unop.left x =
      r • (tilde.map (R := A) (ModuleCat.ofHom φ)).app U.unop.left x
    let s : ModuleCat.of A A ⟶ ModuleCat.of A A :=
      ModuleCat.ofHom (r • LinearMap.id)
    have h : ModuleCat.ofHom (r • φ) = ModuleCat.ofHom φ ≫ s := by
      ext m
      rfl
    rw [h, tilde.map_comp, Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    exact tilde_scalar_section_action A (ModuleCat.of A A) r s (fun m ↦ rfl) _ _

open Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def sectionsTopEquiv (A : CommRingCat.{u}) (H : (Spec A).Modules) :
    H.sections ≃ Γ(H, ⊤) where
  toFun s := s.val (op ⊤)
  invFun x := PresheafOfModules.sectionsMk
    (fun U ↦ H.val.map U.unop.leTop.op x) (by
      intro U V f
      rw [← H.val.map_comp_apply]
      rfl)
  left_inv s := by
    apply Subtype.ext
    funext U
    exact s.property U.unop.leTop.op
  right_inv x := by
    change H.val.map (𝟙 (op ⊤)) x = x
    rw [PresheafOfModules.map_id]
    rfl

open Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem globalSectionLinear_bijective (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    Function.Bijective (affineDualGlobalSectionLinear A M) := by
  let e : Module.Dual A M ≃ Γ(SheafOfModules.homObj (R := (Spec A).sheaf) (tilde M)
      (SheafOfModules.unit (Spec A).ringCatSheaf), ⊤) :=
    ModuleCat.homEquiv.symm |>.trans
      (tilde.fullyFaithfulFunctor (R := A)).homEquiv |>.trans
      (Iso.homCongr (Iso.refl _) tildeSelf) |>.trans
      (SheafOfModules.homObjSectionsEquiv (R := (Spec A).sheaf) _ _).symm |>.trans
      (sectionsTopEquiv A _)
  exact e.bijective

open Opposite in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem affineDualIso
    (A : CommRingCat.{u}) [IsNoetherianRing A] (M : ModuleCat.{u} A)
    [Module.Finite A M] :
    Nonempty (tilde (ModuleCat.of A (Module.Dual A M)) ≅
      SheafOfModules.homObj (R := (Spec A).sheaf) (tilde M)
        (SheafOfModules.unit (Spec A).ringCatSheaf)) := by
  let H : (Spec A).Modules := SheafOfModules.homObj (R := (Spec A).sheaf) (tilde M)
    (SheafOfModules.unit (Spec A).ringCatSheaf)
  have : Module.Finite A Γ(tilde M, ⊤) :=
    Module.Finite.equiv (tilde.isoTop M).toLinearEquiv
  have : (tilde M).IsFinitePresentation := Modules.isFinitePresentation_of_finite _
  have : (SheafOfModules.unit (Spec A).ringCatSheaf).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso tildeSelf inferInstance
  have : H.IsQuasicoherent :=
    Modules.isQuasicoherent_homObj_of_isFinitePresentation (Spec A) _ _
  let β : ModuleCat.of A (Module.Dual A M) ⟶ (moduleSpecΓFunctor (R := A)).obj H :=
    ConcreteCategory.ofHom (affineDualGlobalSectionLinear A M)
  have : IsIso β := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact globalSectionLinear_bijective A M
  have : IsIso (Modules.fromTildeΓ (R := A) H) :=
    Modules.isIso_fromTildeΓ_of_isQuasicoherent H
  exact ⟨(tilde.functor A).mapIso (asIso β) ≪≫ asIso (Modules.fromTildeΓ (R := A) H)⟩

/-- Localization of Hom identifies the restriction of the associated sheaf of the
module dual with the sheaf dual of the restriction. -/
theorem affine_dual_restriction_comparison
    (A : CommRingCat.{u}) [IsNoetherianRing A] (W : (Spec A).Opens)
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    Nonempty (Modules.restrict (tilde (ModuleCat.of A (Module.Dual A M))) W.ι ≅
      SheafOfModules.homObj.{u} (R := W.toScheme.sheaf) (Modules.restrict (tilde M) W.ι)
        (SheafOfModules.unit W.toScheme.ringCatSheaf)) := by
  let H : (Spec A).Modules := SheafOfModules.homObj (R := (Spec A).sheaf) (tilde M)
    (SheafOfModules.unit (Spec A).ringCatSheaf)
  obtain ⟨eA⟩ := affineDualIso A M
  let T := (Modules.overEquiv W).functor
  let O := SheafOfModules.unit (Spec A).ringCatSheaf
  obtain ⟨e, _⟩ := internalHom_overEquiv W
  let eM := (Modules.overFunctorEquiv W).app (tilde M)
  let eO := (Modules.overFunctorEquiv W).app O ≪≫ Modules.restrictUnitIso W.ι
  let eH : T.obj (H.over W) ≅
      SheafOfModules.homObj (R := W.toScheme.sheaf)
        ((tilde M).restrict W.ι) (SheafOfModules.unit W.toScheme.ringCatSheaf) :=
    T.mapIso (SheafOfModules.overHomObjIso (R := (Spec A).sheaf) (tilde M) O W) ≪≫
      e ((tilde M).over W) (O.over W) ≪≫
      ((SheafOfModules.homFunctor W.toScheme.sheaf).mapIso eM.symm.op).app _ ≪≫
      ((SheafOfModules.homFunctor W.toScheme.sheaf).obj
        (Opposite.op ((tilde M).restrict W.ι))).mapIso eO
  exact ⟨(Modules.restrictFunctor W.ι).mapIso eA ≪≫
    ((Modules.overFunctorEquiv W).app H).symm ≪≫ eH⟩

end AlgebraicGeometry.Scheme
