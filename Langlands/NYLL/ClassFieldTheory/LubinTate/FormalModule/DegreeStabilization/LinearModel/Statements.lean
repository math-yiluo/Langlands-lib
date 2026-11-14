/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 491, 2026-11-14: extract the statements of the
source-private theorems M351.012–M351.016 (lines 405–479) from upstream
commit fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued targets
`Langlands.NYLL.PortInternal.M351.d012Statement` … `d016Statement`;
qualify the opened namespaces with Langlands.NYLL; replace the source
imports by the published M351.011 and M348 definition modules and Mathlib's
MvPowerSeries order module; refer to the source-private
`linearInVariableStabilization` by its published name `d011`; omit the
unused local `Classical.propDecidable` instance. Each target keeps the
elaborated binders of its source theorem, including the source omission of
`[Fintype σ]` and the `[Finite σ]` hypothesis of M351.013, and has the source
conclusion as its body. Source proofs are omitted. The original LICENSE and
NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions
import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# Proposition targets for the linear model of `e(X_i)`

Exact proposition targets for the five source-private theorems that follow
the linear model `d011 π i = C π * X_i` in the source module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`: the
linear model has zero constant coefficient and admits substitution, both
`e(X_i)` and the linear model have order at least one, and `e(X_i)` agrees
with its linear model up to order two.
-/

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- Target of M351.012 (`linearInVariableStabilization_constantCoeff`): the
linear model `C π * X_i` has zero constant coefficient. -/
abbrev d012Statement (π : F.valuationSubring) (i : σ) : Prop :=
  MvPowerSeries.constantCoeff (d011 π i) = 0

/-- Target of M351.013 (`linearInVariableStabilization_hasSubst`): for a
finite variable type, the family `i ↦ C π * X_i` admits multivariable
substitution. -/
abbrev d013Statement [Finite σ] (π : F.valuationSubring) : Prop :=
  MvPowerSeries.HasSubst (d011 (σ := σ) π)

/-- Target of M351.014 (`one_le_order_inVariable_stabilization`): the series
`ebar(X_i)` has order at least one. -/
abbrev d014Statement (ebar : LubinTateSeries F π) (i : σ) : Prop :=
  (1 : ℕ∞) ≤ (inVariable ebar i).order

/-- Target of M351.015 (`one_le_order_linearInVariableStabilization`): the
linear model `C π * X_i` has order at least one. -/
abbrev d015Statement (π : F.valuationSubring) (i : σ) : Prop :=
  (1 : ℕ∞) ≤ (d011 π i).order

/-- Target of M351.016
(`two_le_order_inVariable_sub_linearInVariableStabilization`): the series
`ebar(X_i)` and its linear model `C π * X_i` agree up to order two. -/
abbrev d016Statement (ebar : LubinTateSeries F π) (i : σ) : Prop :=
  (2 : ℕ∞) ≤ (inVariable ebar i - d011 π i).order

end Langlands.NYLL.PortInternal.M351
