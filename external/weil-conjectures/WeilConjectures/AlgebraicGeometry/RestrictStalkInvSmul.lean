/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Scalar compatibility of inverse open restriction on stalks

Source: Stacks Project, Tag 0098; Mathlib restriction-stalk germ formulas.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

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

/-- Inverse open restriction on module stalks is semilinear for the actual stalk map.

Proof: first prove semilinearity of the forward restriction comparison over the
inverse stalk ring map. Represent the scalar and restricted module element by germs
on a common source open. The inverse stalk ring map takes the scalar germ to the
ambient germ of the inverse appIso section. The hom restriction-stalk germ formula
and germ_smul on both schemes give the scalar identity for the forward comparison.
Now apply injectivity of that additive comparison to the desired inverse identity.
Use forward semilinearity with scalar j.stalkMap z d and element r(x), where r is
inverse restriction. The inverse equations for the ring map and additive comparison
reduce the resulting identity to the required equality. There is no point on an
empty source; zero rings and zero modules need no assumptions.
The two private germ lemmas reuse the proved arguments in
WeilConjectures.AlgebraicGeometry.OpenSemilinearInputComplexIso (also in
WeilConjectures.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso).
Source: Stacks Project, Tag 0098, restriction of stalks; Mathlib
Scheme.Modules.germ_restrictStalkNatIso_hom_app and PresheafOfModules.germ_smul.
(blueprint: lem-pc-restrict-stalk-inv-smul). -/
theorem restrictStalkNatIso_inv_smul
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (z : Y)
    (M : Z.Modules) (d : Z.presheaf.stalk (j z))
    (x : (RingedSpace.moduleStalkFunctor Z.toRingedSpace (j z)).obj M) :
    (restrictStalkNatIso j z).inv.app M (d • x) =
      (j.stalkMap z).hom d •
        (show (RingedSpace.moduleStalkFunctor Y.toRingedSpace z).obj
          ((restrictFunctor j).obj M) from (restrictStalkNatIso j z).inv.app M x) := by
  apply (ConcreteCategory.bijective_of_isIso ((restrictStalkNatIso j z).hom.app M)).1
  have h := restriction_stalk_smul j z M ((j.stalkMap z).hom d)
    ((restrictStalkNatIso j z).inv.app M x)
  simpa only [← NatIso.inv_hom_app, IsIso.inv_hom_id_apply,
    IsIso.hom_inv_id_apply] using h.symm

end AlgebraicGeometry.Scheme.Modules
