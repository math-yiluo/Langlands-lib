/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Scalar compatibility of the explicit affine stalk transport

Source: Stacks Project, Tags 01BH and 01HV (7).
(blueprint: new-s2-affine-model-stalk-transport-linear)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse stalk ring map acts on germs through the inverse section-ring map. -/
private theorem inverse_stalkMap_germ
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X)
    (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
    (inv (j.stalkMap x)) (X.presheaf.germ U x hx r) =
      Y.presheaf.germ (j ''ᵁ U) (j x) (by simpa) ((j.appIso U).inv r) := by
  apply (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).1
  simp only [IsIso.inv_hom_id_apply]
  rw [Scheme.Hom.germ_stalkMap_apply]
  change X.presheaf.germ U x hx r =
    ((j.appIso U).inv ≫ j.app _ ≫ X.presheaf.germ _ x _) r
  rw [Scheme.Hom.appIso_inv_app_assoc]
  exact (X.presheaf.germ_res_apply (eqToHom (j.preimage_image_eq U)) x
    (by simpa) r).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The additive restriction-stalk comparison is semilinear over the inverse stalk map. -/
private theorem restriction_stalk_smul
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules)
    (r : X.presheaf.stalk x)
    (m : ((Scheme.Modules.restrictFunctor j).obj M).presheaf.stalk x) :
    (Scheme.Modules.restrictStalkNatIso j x).hom.app M (r • m) =
      (inv (j.stalkMap x)) r •
        (show M.presheaf.stalk (j x) from
          (Scheme.Modules.restrictStalkNatIso j x).hom.app M m) := by
  let N := (Scheme.Modules.restrictFunctor j).obj M
  obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hxV, m, rfl⟩ := N.presheaf.exists_germ_eq m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
    ← N.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf) N.val]
  rw [inverse_stalkMap_germ]
  have hg (s : Γ(N, U ⊓ V)) :
      (Scheme.Modules.restrictStalkNatIso j x).hom.app M
        (N.presheaf.germ (U ⊓ V) x hx s) =
        M.presheaf.germ (j ''ᵁ (U ⊓ V)) (j x) (by simpa) s :=
    ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app j x M hx) s
  erw [hg, hg]
  exact PresheafOfModules.germ_smul (R := Y.presheaf) M.val _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Inverting the additive comparison gives semilinearity over the stalk ring map. -/
private theorem restriction_stalk_inv_smul
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules)
    (r : Y.presheaf.stalk (j x)) (m : M.presheaf.stalk (j x)) :
    (Scheme.Modules.restrictStalkNatIso j x).inv.app M (r • m) =
      j.stalkMap x r • (show ((Scheme.Modules.restrictFunctor j).obj M).presheaf.stalk x from
        (Scheme.Modules.restrictStalkNatIso j x).inv.app M m) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((Scheme.Modules.restrictStalkNatIso j x).hom.app M)).1
  rw [restriction_stalk_smul]
  have h (t : M.presheaf.stalk (j x)) :
      (Scheme.Modules.restrictStalkNatIso j x).hom.app M
        ((Scheme.Modules.restrictStalkNatIso j x).inv.app M t) = t :=
    ConcreteCategory.congr_hom
      ((Scheme.Modules.restrictStalkNatIso j x).app M).inv_hom_id t
  rw [h, h]
  simp only [IsIso.hom_inv_id_apply]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The composite chart and inclusion ring maps recover the germ of an affine section. -/
private theorem chart_scalar_germ
    {Y : Scheme.{u}} (x : Y) (U : Y.affineOpens) (hx : x ∈ U.1) (a : Γ(Y, U.1)) :
    (inv (U.1.ι.stalkMap ⟨x, hx⟩))
      (U.2.isoSpec.hom.stalkMap ⟨x, hx⟩
        (StructureSheaf.toStalk Γ(Y, U.1) (U.2.primeIdealOf ⟨x, hx⟩) a)) =
      Y.presheaf.germ U.1 x hx a := by
  apply (ConcreteCategory.bijective_of_isIso (U.1.ι.stalkMap ⟨x, hx⟩)).1
  simp only [IsIso.inv_hom_id_apply]
  change U.2.isoSpec.hom.stalkMap ⟨x, hx⟩
      ((Spec Γ(Y, U.1)).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso _).inv a)) = _
  rw [Scheme.Hom.germ_stalkMap_apply]
  change U.1.toScheme.presheaf.germ ⊤ ⟨x, hx⟩ trivial
    (U.2.isoSpec.hom.appTop ((Scheme.ΓSpecIso _).inv a)) = _
  rw [U.2.isoSpec_hom_appTop, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  erw [Scheme.Hom.germ_stalkMap_apply U.1.ι U.1 ⟨x, hx⟩ hx a]
  have h := U.1.toScheme.presheaf.germ_res_apply
    (eqToHom U.1.ι_preimage_self : U.1.ι ⁻¹ᵁ U.1 ⟶ ⊤)
    (⟨x, hx⟩ : U.1.toScheme) hx (U.1.topIso.inv a)
  rw [← h]
  congr 1
  change (U.1.topIso.inv ≫ U.1.toScheme.presheaf.map (eqToHom U.1.ι_preimage_self).op) a =
    U.1.ι.app U.1 a
  rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_app_self, Scheme.Opens.toScheme_presheaf_map,
    ← Y.presheaf.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The additive stalk transport, constructed from the chart, model, and open restriction. 
(blueprint: new-s2-affine-model-stalk-transport-linear)
-/
noncomputable def affineModelStalkAddEquiv
    {Y : Scheme.{u}} (x : Y) (U : Y.affineOpens) (hx : x ∈ U.1)
    (F : Y.Modules) (M : ModuleCat.{u} Γ(Y, U.1))
    (e : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅
      (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj (tilde M)) :
    (tilde M).presheaf.stalk (U.2.primeIdealOf ⟨x, hx⟩) ≃+ F.presheaf.stalk x :=
  (((Scheme.Modules.restrictStalkNatIso U.2.isoSpec.hom ⟨x, hx⟩).app
      (tilde M)).symm ≪≫
    (Scheme.Modules.toPresheaf U.1.toScheme ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} (⟨x, hx⟩ : U.1.toScheme)).mapIso e.symm ≪≫
    (Scheme.Modules.restrictStalkNatIso U.1.ι ⟨x, hx⟩).app F).addCommGroupIsoToAddEquiv

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The explicitly constructed additive transport respects the coordinate-ring action.
Source: Stacks Project, Tags 01BH and 01HV (7).
(blueprint: new-s2-affine-model-stalk-transport-linear)

Proof: For an open immersion f, restriction-stalk transport carries the germ of
r times m to the germ of the restricted scalar times the transported section.
Represent r and m on a common neighbourhood and apply germ_smul and
smul_restrictAppIso_hom; the germ formula for restrictStalkNatIso gives this
identity in the stalk. Its inverse satisfies the inverse identity by bijectivity.
Apply these identities to the chart isomorphism and to U -> Y, and use linearity
of e.inv on sections for the middle factor. The composite ring-stalk map carries
the canonical germ of a in Spec A to the germ of a on U: this is
isoSpec_hom_appTop followed by germ_stalkMap_apply. Consequently the three
scalar identities compose to the displayed equality. Germ representatives cover
all stalk elements. Zero modules require no exception, and hx rules out empty U. -/
theorem affineModelStalkAddEquiv_smul
    {Y : Scheme.{u}} (x : Y) (U : Y.affineOpens) (hx : x ∈ U.1)
    (F : Y.Modules) (M : ModuleCat.{u} Γ(Y, U.1))
    (e : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅
      (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).obj (tilde M))
    (a : Γ(Y, U.1)) (m : (tilde M).presheaf.stalk (U.2.primeIdealOf ⟨x, hx⟩)) :
    affineModelStalkAddEquiv x U hx F M e (a • m) =
      Y.presheaf.germ U.1 x hx a • affineModelStalkAddEquiv x U hx F M e m := by
  let z : U.1.toScheme := ⟨x, hx⟩
  let r : (Spec Γ(Y, U.1)).presheaf.stalk (U.2.primeIdealOf z) :=
    StructureSheaf.toStalk Γ(Y, U.1) (U.2.primeIdealOf z) a
  have ha : a • m = r • m := rfl
  change (Scheme.Modules.restrictStalkNatIso U.1.ι z).hom.app F
      ((e.inv.stalkLinearMap z)
        ((Scheme.Modules.restrictStalkNatIso U.2.isoSpec.hom z).inv.app (tilde M)
          (a • m))) = _
  rw [ha, restriction_stalk_inv_smul, map_smul, restriction_stalk_smul]
  rw [chart_scalar_germ]
  rfl

end AlgebraicGeometry
