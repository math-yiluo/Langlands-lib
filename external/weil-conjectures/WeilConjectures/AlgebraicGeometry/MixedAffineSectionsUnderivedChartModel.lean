/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-! # Ordinary affine chart extension and sections comparison
Source: Stacks Project, Tags 01I9, 0AA7 and 08DW(2).
(blueprint: lem-sc-mixed-affine-sections-underived-chart-model).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem chart_pushforward_smul (X : Scheme.{u}) (M : X.Modules)
    (a : Γ(X, ⊤)) (m : Γ((Scheme.Modules.pushforward X.toSpecΓ).obj M, ⊤)) :
    a • (show (moduleSpecΓFunctor.obj
        ((Scheme.Modules.pushforward X.toSpecΓ).obj M)) from m) =
      (a • (show Γ(M, ⊤) from m) : Γ(M, ⊤)) := by
  open Scheme.Modules in
    have h1 := congr(Scheme.Modules.Hom.app
      $(pushforward_map_smulHom X.toSpecΓ M ((Scheme.ΓSpecIso Γ(X, ⊤)).inv a)) ⊤ m)
    rw [pushforward_map_app, smulHom_app_apply] at h1
    refine h1.symm.trans ?_
    erw [smulHom_app_apply]
    have h2 : X.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv a) = a := by
      rw [← CommRingCat.comp_apply, Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
      rfl
    rw [h2, show (homOfLE (le_top : X.toSpecΓ ⁻¹ᵁ
      (⊤ : (Spec Γ(X, ⊤)).Opens) ≤ ⊤)).op = 𝟙 _ from Subsingleton.elim _ _]
    erw [CategoryTheory.Functor.map_id]
    rfl

private noncomputable def chart_sections_iso (X : Scheme.{u}) :
    RingedSpace.globalSectionsFunctor X.toRingedSpace ≅
      Scheme.Modules.pushforward X.toSpecΓ ⋙ moduleSpecΓFunctor (R := Γ(X, ⊤)) :=
  NatIso.ofComponents (fun M ↦ LinearEquiv.toModuleIso
    (X₁ := (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M)
    (X₂ := moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward X.toSpecΓ).obj M))
    { __ := AddEquiv.refl _
      map_smul' a m := (chart_pushforward_smul X M a m).symm })
    (by intro M N f; rfl)

private noncomputable def chart_tilde_adjunction (X : Scheme.{u}) [IsAffine X] :
    tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.restrictFunctor X.toSpecΓ ⊣
      RingedSpace.globalSectionsFunctor X.toRingedSpace :=
  ((tilde.adjunction (R := Γ(X, ⊤))).comp
    (Scheme.Modules.restrictAdjunction X.toSpecΓ)).ofNatIsoRight (chart_sections_iso X).symm

private theorem chart_tilde_unit_isIso (X : Scheme.{u}) [IsAffine X] :
    IsIso (chart_tilde_adjunction X).unit := by
  let R := Scheme.Modules.restrictFunctor X.toSpecΓ
  let R' := Scheme.Modules.restrictFunctor X.isoSpec.inv
  let e : (Spec Γ(X, ⊤)).Modules ≌ X.Modules := CategoryTheory.Equivalence.mk R R'
    ((Scheme.Modules.restrictFunctorId).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by
        rw [← Scheme.isoSpec_hom]; exact X.isoSpec.inv_hom_id.symm) ≪≫
      Scheme.Modules.restrictFunctorComp X.isoSpec.inv X.toSpecΓ)
    ((Scheme.Modules.restrictFunctorComp X.toSpecΓ X.isoSpec.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr X.toSpecΓ_isoSpec_inv ≪≫
      Scheme.Modules.restrictFunctorId)
  let : R.IsEquivalence := e.isEquivalence_functor
  let : (tilde.functor Γ(X, ⊤)).Full := (tilde.fullyFaithfulFunctor (R := Γ(X, ⊤))).full
  let : (tilde.functor Γ(X, ⊤)).Faithful :=
    (tilde.fullyFaithfulFunctor (R := Γ(X, ⊤))).faithful
  exact Adjunction.unit_isIso_of_L_fully_faithful (chart_tilde_adjunction X)

-- The affine carrier identifications require extra elaboration time.
/-- The unit-normalized comparison between ordinary scalar extension of sections
and sections of tensor pullback, on the canonical affine chart sheafification.
Source: Stacks Project, Tags 01I9 and 0AA7, the affine computation in Tag 08DW(2).
(blueprint: lem-sc-mixed-affine-sections-underived-chart-model).

Proof: Put F_X = tilde followed by restriction along X.toSpecΓ. Since X is affine,
restriction is an equivalence. Transport the tilde/sections adjunction through this
equivalence; the right adjoint is ordinary Gamma_X, with scalars identified by
GammaSpecIso and the identity GammaSpecIso.inv followed by X.toSpecΓ.appTop = id.
The unit is invertible, as is the original tilde unit. Do this for S and T.
Compose F_S ⊣ Gamma_S with tensor pullback/direct image along g. Direct image
followed by Gamma_S is Gamma_T followed by restriction along g.appTop, identically
on sections. Compare this composite adjunction with scalar extension/restriction
composed with F_T ⊣ Gamma_T. Left-adjoint uniqueness gives an isomorphism from
scalar extension followed by F_T to F_S followed by tensor pullback, with the unit
equation. Apply Gamma_T to this isomorphism. Precompose with the inverse Gamma_S
unit under scalar extension and the Gamma_T unit under scalar extension. The
result is c. Naturality of the extension unit and the unit equation for
left-adjoint uniqueness give the displayed identity. This uses the actual fixed
tensor-pullback adjunction, so no arbitrary normalization of c is allowed. Both
zero rings and zero modules satisfy these adjunction identities. -/
theorem exists_mixedAffineSections_underived_chart_model
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T] (g : T ⟶ S) :
    let F : ModuleCat.{u} Γ(S, ⊤) ⥤
        SheafOfModules.{u} (moduleRings S.toRingedSpace) :=
      tilde.functor Γ(S, ⊤) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ
    let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
    let J := RingedSpace.globalSectionsFunctor T.toRingedSpace
    let E := ModuleCat.extendScalars.{u, u, u} g.appTop.hom
    let K : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
    ∃ c : F ⋙ H ⋙ E ≅ F ⋙ K ⋙ J,
      ∀ N : ModuleCat.{u} Γ(S, ⊤),
        (ModuleCat.extendRestrictScalarsAdj g.appTop.hom).unit.app (H.obj (F.obj N)) ≫
          (ModuleCat.restrictScalars.{u} g.appTop.hom).map (c.hom.app N) =
        H.map ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
          (F.obj N)) := by
  classical
  dsimp only
  let F : ModuleCat.{u} Γ(S, ⊤) ⥤ S.Modules :=
    tilde.functor Γ(S, ⊤) ⋙ Scheme.Modules.restrictFunctor S.toSpecΓ
  let FT : ModuleCat.{u} Γ(T, ⊤) ⥤ T.Modules :=
    tilde.functor Γ(T, ⊤) ⋙ Scheme.Modules.restrictFunctor T.toSpecΓ
  let H := RingedSpace.globalSectionsFunctor S.toRingedSpace
  let J := RingedSpace.globalSectionsFunctor T.toRingedSpace
  let E := ModuleCat.extendScalars.{u, u, u} g.appTop.hom
  let R := ModuleCat.restrictScalars.{u} g.appTop.hom
  let K : S.Modules ⥤ T.Modules := Scheme.Modules.tensorPullback g
  let V : Scheme.Modules.pushforward g ⋙ H ≅ J ⋙ R := Iso.refl _
  let br : F ⊣ H := chart_tilde_adjunction S
  let bb : FT ⊣ J := chart_tilde_adjunction T
  let : IsIso br.unit := chart_tilde_unit_isIso S
  let : IsIso bb.unit := chart_tilde_unit_isIso T
  let e : E ⊣ R := ModuleCat.extendRestrictScalarsAdj g.appTop.hom
  let p : K ⊣ Scheme.Modules.pushforward g :=
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let a₁ := (br.comp p).ofNatIsoRight V
  let a₂ := e.comp bb
  let θ := a₂.leftAdjointUniq a₁
  let c : F ⋙ H ⋙ E ≅ F ⋙ K ⋙ J :=
    Functor.isoWhiskerRight (asIso br.unit).symm E ≪≫ Functor.leftUnitor E ≪≫
      (Functor.rightUnitor E).symm ≪≫ Functor.isoWhiskerLeft E (asIso bb.unit) ≪≫
        Functor.isoWhiskerRight θ J
  refine ⟨c, ?_⟩
  intro N
  have h := a₂.unit_leftAdjointUniq_hom_app a₁ N
  change e.unit.app N ≫ R.map (bb.unit.app (E.obj N)) ≫
      R.map (J.map (θ.hom.app N)) =
    br.unit.app N ≫ H.map (p.unit.app (F.obj N)) ≫
      V.hom.app (K.obj (F.obj N)) at h
  change e.unit.app (H.obj (F.obj N)) ≫ R.map (c.hom.app N) =
    H.map (p.unit.app (F.obj N))
  dsimp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app]
  simp only [Category.id_comp, Functor.map_comp]
  change e.unit.app (H.obj (F.obj N)) ≫
      R.map (E.map ((asIso br.unit).inv.app N)) ≫
        R.map (bb.unit.app (E.obj N)) ≫ R.map (J.map (θ.hom.app N)) = _
  have hn := e.unit.naturality ((asIso br.unit).inv.app N)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  change (asIso br.unit).inv.app N ≫ e.unit.app N =
    e.unit.app (H.obj (F.obj N)) ≫
      R.map (E.map ((asIso br.unit).inv.app N)) at hn
  rw [← Category.assoc, ← hn, Category.assoc, h]
  change (((asIso br.unit).inv.app N ≫ (asIso br.unit).hom.app N) ≫
    H.map (p.unit.app (F.obj N))) ≫ 𝟙 _ = _
  rw [Iso.inv_hom_id_app, Category.id_comp, Category.comp_id]

end AlgebraicGeometry

