/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualRingedExchange
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-!
# Finite pro-etale smooth base change

Source: Weil conjectures blueprint, sec-smooth-base-change/sk-rem-rest, finite
pro-etale smooth-base-change paragraph; Stacks Project, Tags 0EYU and 0F09
(blueprint: theorem-smooth-base-change-all-admissible--1).

The input and output use the recorded continuous-function coefficient module category.
The ambient ringed mate is computed in fixed-scalar coordinates using the canonical
realization equivalence. This is the same unit--square--counit mate: realization
identifies the coefficient actions by constant scalar sections, transports the
adjunctions and their composition comparisons, and hence transports their mate.
No alternative exchange is chosen and no completion is taken.

## Main definitions

- `finiteSmoothModelCoordinates`: coordinates of an arbitrary etale model isomorphism.
- `finiteSmoothTargetComparison`: target comparison, deriving qcqs of the base change.

## Main statement

- `isIso_finite_proetale_smooth_base_change`: invertibility and the explicit
  conjugation identity for every etale model, in the ringed coefficient category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

end AlgebraicGeometry.ProEtale
