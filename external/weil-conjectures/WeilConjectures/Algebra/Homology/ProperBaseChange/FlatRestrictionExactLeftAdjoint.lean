/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Exact left adjoints to flat coefficient restriction

Source: Stacks Project, Modules on Sites, Tag 03CZ; Definition 03ER(3).
(blueprint: lem-weil-pbc-flat-restriction-exact-left-adjoint).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ChangeOfRings

private noncomputable abbrev rb
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K CommRingCat.{u}) :=
  (sheafCompose K (forget₂ CommRingCat RingCat)).obj R

section Construction

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
  {R S : Sheaf K CommRingCat.{u}} (a : R ⟶ S)

private noncomputable abbrev scalarUnit : SheafOfModules.{u} (rb R) :=
  (restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map a)).obj (unit (rb S))

end Construction

end SheafOfModules
