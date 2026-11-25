/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # Composite direct-image units with a fixed source

Source: Stacks Project, Cohomology, Tag 0D5T.
(blueprint: def-pc-direct-image-composition-unit-source).
-/

@[expose] public section

universe u w
open CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

-- Comparing the whole and successive pushforwards expands scalar restrictions once.
/-- The existing composite derived unit, with its source expressed by successive images.
The source identification is definitional: pushforward composition is the identity
on sections. Naming it prevents later categorical calculations from repeatedly
unfolding scalar restrictions.
Source: Stacks Project, Cohomology, Tag 0D5T.
(blueprint: def-pc-direct-image-composition-unit-source). -/
@[irreducible] def schemeMVCompositionUnit {A B D : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings A.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings B.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings D.toRingedSpace))]
    (s : A ⟶ B) (t : B ⟶ D)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (fun {V W : Type _} [Category V] [Category W] {P Q : V ⥤ W}
      (_ : P ⟶ Q) (J : V) ↦ P.obj J)
      (RingedSpace.moduleDirectImage t.toLRSHom.toShHom).rightDerivedFunctorUnit
      (((RingedSpace.moduleDirectImage s.toLRSHom.toShHom).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K) ⟶
      (schemeDerivedDirectImage (s ≫ t)).obj (DerivedCategory.Qh.obj K) :=
  (RingedSpace.moduleDirectImage (s ≫ t).toLRSHom.toShHom).rightDerivedFunctorUnit.app K

end AlgebraicGeometry
