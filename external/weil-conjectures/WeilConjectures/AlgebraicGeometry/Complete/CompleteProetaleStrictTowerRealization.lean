/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenStrictMateIdentification
import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerRealizationComparisons
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization

/-! # Strict-tower realization of the ordered completed proper/open composite

Source: blueprint sec-six-functors-basics/sk-prop-sf-cbc, Definition 1939;
Stacks 03DI, 09BP, 0A07.
(blueprint: lem-cbc-complete-proetale-strict-tower-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.StrictTower
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}

end AlgebraicGeometry.Scheme
