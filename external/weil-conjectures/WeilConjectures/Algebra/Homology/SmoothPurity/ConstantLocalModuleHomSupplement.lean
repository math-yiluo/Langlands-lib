/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalModuleIsoSupplement
public import WeilConjectures.CategoryTheory.ConstantLocalModuleHom

/-! # Constant sections of local module Hom and Isom presheaves

Source: Stacks Project, Modules on Sites, Tag 093T.
(blueprint: lem-sf-constant-local-module-isom-bijective).
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {D : Type v} [Category.{u} D]
  (F : D ⥤ SheafOfModules.{u} R) (M N P : D)

end SheafOfModules
