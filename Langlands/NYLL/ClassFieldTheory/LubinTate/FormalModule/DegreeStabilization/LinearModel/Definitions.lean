/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 491, 2026-11-14: extract only the source-private
definition M351.011 (`linearInVariableStabilization`, lines 400–403) from
upstream commit fbd320cd8b1b06487c58227e92eb135794267709; rename it to
`Langlands.NYLL.PortInternal.M351.d011` and remove the `private` modifier;
qualify the opened namespace with Langlands.NYLL; replace the source
imports (RecursiveCoefficient and MvPowerSeries.Trunc) by the published
LocalField definition module and Mathlib's MvPowerSeries basics; declare
only the section variables of the elaborated source type (the shadowed
section `π` and the unused section instance `[Fintype σ]` are dropped by
Lean in the source as well); omit the unused local
`Classical.propDecidable` instance and all other source declarations; and
replace the module documentation. The body and type are unchanged. The
original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# The linear model of a Lubin--Tate series in one variable

For an element `π` of the valuation subring of a local field, this module
defines the multivariable power series `π • X_i = C π * X_i`. It is the linear
part of the series `e(X_i)` obtained by inserting a Lubin--Tate series with
linear coefficient `π` into the variable `X_i`, and is used to compare
substitutions with their linear model in the degree-stabilization argument.
-/

noncomputable section

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {σ : Type w}

/-- M351.011 (source-private `linearInVariableStabilization`): the linear
series `C π * X_i` in the variables `σ` over the valuation subring. -/
noncomputable def d011
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.C π * MvPowerSeries.X i

end Langlands.NYLL.PortInternal.M351

end
