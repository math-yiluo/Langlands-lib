/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# Open-immersion squares
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An open-immersion square is a chosen Cartesian square with both vertical arrows
open immersions. The inherited datum includes `gU ≫ j = j' ≫ g`, a chosen isomorphism
`U' ≅ CategoryTheory.Limits.pullback j g`, and its compatibility with both projections.
No condition is imposed on the bottom arrow `g`. -/
structure OpenImmersionSquare {U' U X' X : Scheme.{u}}
    (gU : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    extends ChosenCartesianSquare gU j' j g where
  /-- The right vertical arrow is an open immersion. -/
  isOpenImmersion : IsOpenImmersion j
  /-- The left vertical arrow is an open immersion. -/
  isOpenImmersion' : IsOpenImmersion j'

end AlgebraicGeometry
