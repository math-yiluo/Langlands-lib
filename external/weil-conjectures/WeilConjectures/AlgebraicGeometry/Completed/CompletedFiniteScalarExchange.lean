/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedFiniteExchangeCoordinates
import WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Ordinary completed-to-finite scalar compatibility

The coefficient projection intertwines the normalized ordinary inverse exchanges.
Source: Stacks Project, Modules on Sites, Tags 03DI, 03D7 and 04J0;
blueprint finite-exchange identification before derived inverse limits.
(blueprint: lem-cbc-completed-finite-scalar-exchange).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

open AlgebraicGeometry.ProEtale.StrictTower

end AlgebraicGeometry.Scheme
