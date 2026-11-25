/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocalModuleHom

/-! # Local isomorphisms of module sheaves

Source: Stacks Project, Modules on Sites, Tag 093T, inverse-pair description.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} (M N : SheafOfModules.{u} R)

/-- Restriction of a local module isomorphism. -/
def restrictIso {U V : Cᵒᵖ} (f : U ⟶ V) (a : M.over U.unop ≅ N.over U.unop) :
    M.over V.unop ≅ N.over V.unop :=
  ((overFunctorMap R f.unop).app M).symm ≪≫ (overMap R f.unop).mapIso a ≪≫
    (overFunctorMap R f.unop).app N

end SheafOfModules
