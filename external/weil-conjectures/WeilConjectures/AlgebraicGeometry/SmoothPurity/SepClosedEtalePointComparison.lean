/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Category
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField

/-! # Comparing etale points after extending a separably closed field

Source: Stacks Project, Tag 04FN; etale lifts are unchanged by extending a separably
closed field. (blueprint: lem-exc-sep-closed-etale-point-comparison)
-/

@[expose] public section

universe u w t

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {k k' : Type u} [Field k] [IsSepClosed k]
  [Field k'] [IsSepClosed k']
  (s : Spec (.of k) ⟶ S) (s' : Spec (.of k') ⟶ S)
  (β : CommRingCat.of k ⟶ CommRingCat.of k') (hβ : Spec.map β ≫ s = s')

end AlgebraicGeometry.Scheme
