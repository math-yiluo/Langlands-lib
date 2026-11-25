/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourArrows
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteReductionPullbackSquare
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube

/-! The finite projection/exchange rectangle in the intrinsic quotient-ring coordinates.
Source: Stacks Project, Tag 0E48.
(blueprint: lem-weil-pbc-intrinsic-finite-exchange-rectangle) -/

@[expose] public noncomputable section
set_option autoImplicit false

-- Avoid replaying the large dependent coefficient transports for tactic linting.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme
attribute [local instance 2000] proEtaleRingModules_hasDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingModulePullback proEtaleRingDerivedAdjunction
  proEtaleAmbientRingedPullbackComparison completedAdicDerivedChange

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

end AlgebraicGeometry.Scheme
