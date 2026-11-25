/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

import WeilConjectures.AlgebraicGeometry.AffineLocalizingPresheafSheafification
import WeilConjectures.LinearAlgebra.ExteriorPowerLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # The exterior sheafification unit on an affine open

## References

* Stacks Project, Tag 01I6, Lemmas 26.7.2(2) and 26.7.4
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The canonical exterior sheafification unit is bijective on affine sections of a
quasi-coherent module. -/
theorem exteriorSheaf_affine_unit_bijective {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (U : X.affineOpens) :
    Function.Bijective
      (((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)).unit.app
        (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)).app (op U.1)) := by
  have hlocal (W : X.Opens) (hW : IsAffineOpen W) (a : Γ(X, W)) :
      IsLocalizedModule.Away a
        ((_root_.PresheafOfModules.exteriorPower (R := _) M.val n).map
          (homOfLE (X.basicOpen_le a)).op).hom := by
    let f := (homOfLE (X.basicOpen_le a)).op
    let := hW.isLocalization_basicOpen a
    let : IsLocalizedModule.Away a (M.val.map f).hom :=
      isLocalizedModule_basicOpen M hW a
    change IsLocalizedModule.Away a
      ((_root_.PresheafOfModules.exteriorPower (R := _) M.val n).map f).hom
    exact exteriorPower.isLocalizedModule_of_wedge
      (R := Γ(X, W)) (B := Γ(X, X.basicOpen a)) (Submonoid.powers a)
      (M.val.obj (op W)) (M.val.obj (op (X.basicOpen a))) (M.val.map f) n
      ((_root_.PresheafOfModules.exteriorPower (R := _) M.val n).map f)
      ((_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := _) M.val n f))
  let := isIso_sheafificationUnit_app_of_affine_localizing X
    (_root_.PresheafOfModules.exteriorPower (R := _) M.val n) hlocal U.1 U.2
  exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry.Scheme.Modules
