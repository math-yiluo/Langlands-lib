/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.FieldTheory.KrullTopology
import Mathlib.CategoryTheory.Sites.Point.Category
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The canonical Galois action functor on geometric stalks

Source: Stacks Project, Tag 03QW.
-/

@[expose] public section

attribute [instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
