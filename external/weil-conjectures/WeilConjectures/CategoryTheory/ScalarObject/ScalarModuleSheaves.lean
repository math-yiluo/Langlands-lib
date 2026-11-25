/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarObject.ScalarObjects
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-! # Module sheaves as scalar objects in abelian sheaves

Source: Stacks Project, Tag 04JQ, transport of module structures.
(blueprint: lem-exc-scalar-module-sheaves)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w r

open CategoryTheory Opposite

namespace CategoryTheory.ScalarObject

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R]

end CategoryTheory.ScalarObject
