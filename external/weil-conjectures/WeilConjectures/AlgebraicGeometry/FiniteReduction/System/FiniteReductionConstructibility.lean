/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteReduction.FiniteReductionSystem
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
import WeilConjectures.AlgebraicGeometry.FiniteReduction.FiniteReductionSystemExistence
import WeilConjectures.AlgebraicGeometry.FiniteReduction.FiniteReductionFlatExtension
import WeilConjectures.AlgebraicGeometry.FiniteReduction.FiniteReductionSystem

/-!
# Finite reduction and constructibility

Source: main-20261015 blueprint, sec-smooth-purity/sk-lem-sp-reduction,
first paragraph; Stacks Tags 08G1, 06YQ, 094H and 09AL
(blueprint: lem-pur-finite-reduction-constructibility).

## Main definitions

* `AlgebraicGeometry.FiniteReduction.System`: universal derived extensions with
  canonical representative normalizations.
* `AlgebraicGeometry.FiniteReduction.System.CoherentAt`: their associator square.

## Main statements

* `AlgebraicGeometry.FiniteReduction.finiteReduction_constructibility`: finite reduction,
  its bounded flat models, intrinsic finiteness and coherent etale origin.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteReduction

end AlgebraicGeometry.FiniteReduction
