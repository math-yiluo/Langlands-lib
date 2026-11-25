/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCofinalData
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleCofinalSupportRealization
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemCofinalData
import WeilConjectures.NumberTheory.Padics.LocalFieldCoefficientStages

/-! # Cofinal compact-support adjunction mates

The geometric interfaces are re-exported from EtaleSystemCofinalData.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a av b bv c cv d dv
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.Etale.SystemProjection

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
section FormalMate
variable
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
    {LX : C ⥤ A} {UX : A ⥤ C} {LY : D ⥤ B} {UY : B ⥤ D}
    {F : A ⥤ B} {G : B ⥤ A} {F' : C ⥤ D} {G' : D ⥤ C}
    (x : LX ⊣ UX) (y : LY ⊣ UY) (f : F ⊣ G) (g : F' ⊣ G')
    (h : LX ⋙ F ≅ F' ⋙ LY)

end FormalMate

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
end AlgebraicGeometry.Etale.SystemProjection
