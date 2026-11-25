/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalModuleHomSupplement
public import WeilConjectures.CategoryTheory.LocalModuleIso

/-! # Local isomorphisms of module sheaves

Source: Stacks Project, Modules on Sites, Tag 093T, inverse-pair description.
(blueprint: lem-sf-local-module-isom-sheaf).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} (M N : SheafOfModules.{u} R)

end SheafOfModules
