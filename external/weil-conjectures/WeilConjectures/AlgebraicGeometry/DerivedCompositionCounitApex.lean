/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso

/-! # The explicit pasted underived counit expression
Source: Stacks Project, Tags 079W, 0D5S and 0D5T.
(blueprint: def-sc-derived-composition-counit-apex).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry
variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

-- The selected scheme counits have large dependent types.
/-- The explicit expression obtained by pasting the localized underived counits.
This names a concrete morphism made from the already recorded choices of counits
and adjunctions. It makes no new existential choice.
Source: Stacks Project, Tags 079W and 0D5S.
(blueprint: def-sc-derived-composition-counit-apex). -/
noncomputable def derivedCompositionCounitApex
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (derivedPullback g ⋙ derivedPullback f).obj
      (DerivedCategory.Qh.obj
        (((Scheme.Modules.pushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          (((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K))) ⟶
      DerivedCategory.Qh.obj K :=
    let ε {A B : Scheme.{u}} (s : A ⟶ B) :=
      (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
    let b {A B : Scheme.{u}} (s : A ⟶ B) :=
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)).mapHomotopyCategory
        (ComplexShape.up ℤ)
    let H := ((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K
    let M := ((Scheme.Modules.pushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).obj H
    (derivedPullback f).map ((ε g).app M ≫
        (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).map
          ((b g).counit.app H)) ≫
        (ε f).app H ≫ DerivedCategory.Qh.map ((b f).counit.app K)

-- The construction equation elaborates the same dependent counit types.
/-- The construction equation for the explicit counit expression.
Source: Stacks Project, Tags 079W and 0D5S.
(blueprint: def-sc-derived-composition-counit-apex). -/
theorem derivedCompositionCounitApex_eq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let ε {A B : Scheme.{u}} (s : A ⟶ B) :=
      (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
    let b {A B : Scheme.{u}} (s : A ⟶ B) :=
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)).mapHomotopyCategory
        (ComplexShape.up ℤ)
    let H := ((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K
    let M := ((Scheme.Modules.pushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).obj H
    derivedCompositionCounitApex f g K =
      (derivedPullback f).map ((ε g).app M ≫
        (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))).map
          ((b g).counit.app H)) ≫
        (ε f).app H ≫ DerivedCategory.Qh.map ((b f).counit.app K) := rfl

attribute [irreducible] derivedCompositionCounitApex

end AlgebraicGeometry
