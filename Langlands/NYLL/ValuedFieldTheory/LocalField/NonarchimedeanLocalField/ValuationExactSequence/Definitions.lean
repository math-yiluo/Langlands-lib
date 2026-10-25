/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 449, 2026-10-25: extract only the two bundled valuation
definitions from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL and replace source imports with
Mathlib.NumberTheory.LocalField.Basic. The construction bodies are unchanged.
The retained license and notices are in licenses/NYLL/.
-/

import Mathlib.NumberTheory.LocalField.Basic

/-!
# Bundled normalized valuation maps on field units

This module adapts only M134.001–002, lines 30–41 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ValuationExactSequence.lean`.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- The multiplicative normalized valuation on field units. -/
noncomputable def valuationUnitsMulHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ →* Multiplicative Int :=
  (@WithZero.unitsWithZeroEquiv (Multiplicative Int) _).toMonoidHom.comp
    ((Units.map (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidHom).comp
      (Units.map (ValuativeRel.valuation K).toMonoidWithZeroHom.toMonoidHom))

/-- The actual normalized valuation map on field units, bundled as an additive hom. -/
noncomputable def valuationMap (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Additive Kˣ →+ Int :=
  MonoidHom.toAdditive (valuationUnitsMulHom K)

end IsNonarchimedeanLocalField

end

end Langlands.NYLL.LocalFieldTheory
