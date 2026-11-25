/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarObject.ScalarObjects
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-! # Scalar objects in discrete representations

Source: Stacks Project, Tag 04JQ, scalar enhancement.
(blueprint: lem-exc-scalar-discrete-representations)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe r g w
open CategoryTheory

namespace CategoryTheory.ScalarObject

variable (R : Type r) [Ring R] (G : Type g) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

end CategoryTheory.ScalarObject
