/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGsets
import WeilConjectures.AlgebraicGeometry.FieldEquivariantGermFamilySection
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-! Fullness of the canonical Galois stalk functor.
Source: Stacks Project, Tags 03QT and 04JM (blueprint: lem-exc-galois-stalk-action-full).
-/

@[expose] public section

attribute [instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
