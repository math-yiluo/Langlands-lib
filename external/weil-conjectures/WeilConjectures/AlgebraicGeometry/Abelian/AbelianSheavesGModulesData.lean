/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianSheavesGModulesTransport
import Mathlib.Algebra.Category.Grp.LeftExactFunctor
import Mathlib.Algebra.Category.Grp.AB

/-!
# Lifting a stalk equivalence to abelian group objects

Source: Stacks Project, Tag 04JQ, the formal transport step.
-/

@[expose] public section

attribute [instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
