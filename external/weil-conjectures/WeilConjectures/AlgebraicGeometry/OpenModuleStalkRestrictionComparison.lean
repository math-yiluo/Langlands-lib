/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor

/-! # Comparing open module stalks under restriction

Source: Stacks Project, Tag 00A0(3), stalks of restrictions to open subspaces.
(blueprint: lem-sc-open-module-stalk-restriction-comparison).
-/

public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

noncomputable section

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Expose the existing presheaf-module stalk instance through `Scheme.Modules.presheaf`. -/
private local instance schemeModuleStalkModule {X : Scheme.{u}} (M : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (M.presheaf.stalk x) :=
  inferInstanceAs (Module (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X)
      (M.val : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ _ _)).presheaf x))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The additive stalk comparison, viewed as a linear map after restriction of scalars. -/
private noncomputable def restrictionStalkLinearMap
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules) :
    (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          ((Scheme.Modules.restrictFunctor j).obj M)) ⟶
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
        ((Scheme.Modules.restrictFunctor j).obj M)))
    (Y := (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M)
    { toFun := (Scheme.Modules.restrictStalkNatIso j x).hom.app M
      map_add' := map_add _
      map_smul' := fun r m ↦ by
        change (Scheme.Modules.restrictStalkNatIso j x).hom.app M
            ((j.stalkMap x) r •
              (show ((Scheme.Modules.restrictFunctor j).obj M).presheaf.stalk x from m)) =
          r • (show M.presheaf.stalk (j x) from
            (Scheme.Modules.restrictStalkNatIso j x).hom.app M m)
        rw [restriction_stalk_smul]
        simp }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The linear stalk comparison is invertible because its underlying additive map is. -/
private noncomputable def restrictionStalkLinearIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) (M : Y.Modules) :
    (ModuleCat.restrictScalars (j.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          ((Scheme.Modules.restrictFunctor j).obj M)) ≅
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x)).obj M := by
  let a := restrictionStalkLinearMap j x M
  have : IsIso a :=
    (ConcreteCategory.isIso_iff_bijective a).mpr
      (ConcreteCategory.bijective_of_isIso
        ((Scheme.Modules.restrictStalkNatIso j x).hom.app M))
  exact asIso a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The linear stalk comparisons are natural in the module sheaf. -/
private noncomputable def restrictionStalkLinearNatIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    (Scheme.Modules.restrictFunctor j ⋙ RingedSpace.moduleStalkFunctor X.toRingedSpace x) ⋙
        ModuleCat.restrictScalars (j.stalkMap x).hom ≅
      RingedSpace.moduleStalkFunctor Y.toRingedSpace (j x) :=
  NatIso.ofComponents (restrictionStalkLinearIso j x) (by
    intro M N f
    ext m
    exact ConcreteCategory.congr_hom
      ((Scheme.Modules.restrictStalkNatIso j x).hom.naturality f) m)



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting a module sheaf to a smaller open does not change its stalk,
with both stalks regarded as modules over the ambient scheme's stalk ring.

Source: Stacks Project, Tag 00A0(3) (restriction to an open subspace),
also for sheaves of modules as specified there.
(blueprint: lem-sc-open-module-stalk-restriction-comparison).

Proof: Apply Scheme.Modules.overMapCompOverEquiv to identify restriction on
slice sites with restriction along the open immersion V.toScheme to W.toScheme.
The neighbourhoods of x contained in V are cofinal among those contained in W.
The resulting colimit comparison on underlying abelian groups is the natural
isomorphism Scheme.Modules.restrictStalkNatIso. Its formula on germs shows that
it respects multiplication by germs of structure-sheaf sections. The composite
of the two open-immersion stalk-ring maps is the ambient stalk-ring map, so after
restriction of scalars both sides are modules over the identical ring O_X,x.
This supplies inverse linear maps and their naturality on every sheaf morphism.
The construction also applies to V=W, when the comparison is the identity. -/
def openModuleStalkRestrictionComparison
    (X : Scheme.{u}) (W V : X.Opens) (hVW : V ≤ W)
    (x : X) (hxW : x ∈ W) (hxV : x ∈ V) :
    SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hVW : V ⟶ W) ⋙ openModuleStalkFunctor X V ⟨x, hxV⟩ ≅
      openModuleStalkFunctor X W ⟨x, hxW⟩ := by
  let j : V.toScheme ⟶ W.toScheme := (X.homOfLE hVW).copyBase
    (fun y ↦ ⟨y.1, hVW y.2⟩) (by
      ext y
      exact Scheme.homOfLE_apply' hVW y.1 y.2)
  have hj : j = X.homOfLE hVW := Scheme.Hom.copyBase_eq _ _ _
  have : IsOpenImmersion j := by rw [hj]; infer_instance
  let v : V.toScheme := ⟨x, hxV⟩
  have hjι : j ≫ W.ι = V.ι := by rw [hj, Scheme.homOfLE_ι]
  have hρ : (V.ι.stalkMap v).hom =
      (j.stalkMap v).hom.comp (W.ι.stalkMap (j v)).hom := by
    have h := Scheme.Hom.stalkMap_congr_hom V.ι (j ≫ W.ι) hjι.symm v
    rw [TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_refl] at h
    have h' : V.ι.stalkMap v = (j ≫ W.ι).stalkMap v :=
      h.trans (Category.id_comp _)
    rw [Scheme.Hom.stalkMap_comp] at h'
    exact congrArg CommRingCat.Hom.hom h'
  let A := (Modules.overEquiv W).functor
  let B := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
    (homOfLE hVW : V ⟶ W)
  let C := (Modules.overEquiv V).functor
  let S := RingedSpace.moduleStalkFunctor V.toScheme.toRingedSpace v
  let T := RingedSpace.moduleStalkFunctor W.toScheme.toRingedSpace (j v)
  let R := ModuleCat.restrictScalars (V.ι.stalkMap v).hom
  let Rj := ModuleCat.restrictScalars (j.stalkMap v).hom
  let Rw := ModuleCat.restrictScalars (W.ι.stalkMap (j v)).hom
  let e₁ : B ⋙ C ≅ A ⋙ Modules.restrictFunctor j :=
    by simpa only [hj] using Modules.overMapCompOverEquiv (homOfLE hVW)
  let e₂ : R ≅ Rj ⋙ Rw := ModuleCat.restrictScalarsComp' _ _ _ hρ
  let e₃ : (Modules.restrictFunctor j ⋙ S) ⋙ Rj ≅ T :=
    restrictionStalkLinearNatIso j v
  let e : B ⋙ (C ⋙ S ⋙ R) ≅ A ⋙ (T ⋙ Rw) :=
    (Functor.associator B C (S ⋙ R)).symm ≪≫
      Functor.isoWhiskerRight e₁ (S ⋙ R) ≪≫
      Functor.associator A (Modules.restrictFunctor j) (S ⋙ R) ≪≫
      Functor.isoWhiskerLeft A (
        (Functor.associator (Modules.restrictFunctor j) S R).symm ≪≫
        Functor.isoWhiskerLeft (Modules.restrictFunctor j ⋙ S) e₂ ≪≫
        (Functor.associator (Modules.restrictFunctor j ⋙ S) Rj Rw).symm ≪≫
        Functor.isoWhiskerRight e₃ Rw)
  exact e

end
end AlgebraicGeometry.Scheme
