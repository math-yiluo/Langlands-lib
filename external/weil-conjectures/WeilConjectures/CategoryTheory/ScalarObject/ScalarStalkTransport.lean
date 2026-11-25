/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarObject.ScalarModuleSheaves
public import WeilConjectures.CategoryTheory.ScalarObject.ScalarDiscreteRepresentations
public import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.Grp.AB

/-! # Scalar enhancement of a geometric stalk equivalence

Source: Stacks Project, Tag 04JQ, transport of scalars across the abelian equivalence.
(blueprint: lem-exc-scalar-stalk-transport)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v
open CategoryTheory Opposite

namespace CategoryTheory.ScalarObject

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  (p : GrothendieckTopology.Point.{u} J)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (R : Type v) [CommRing R]

end CategoryTheory.ScalarObject
