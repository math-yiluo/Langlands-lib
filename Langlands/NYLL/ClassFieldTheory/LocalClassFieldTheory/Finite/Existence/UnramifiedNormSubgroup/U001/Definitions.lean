/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-13: extract M266.001 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and replace source imports by the published valuation
map definitions and Mathlib.Data.ZMod.Basic. The definition is unchanged.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions
import Mathlib.Data.ZMod.Basic

/-!
# Normalized valuation reduced modulo a degree

This module adapts only M266.001, source lines 30–34 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

noncomputable section

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The normalized valuation map reduced modulo a positive or zero degree n. -/
noncomputable def valuationModDegree (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) :
    Additive Kˣ →+ ZMod n :=
  (Int.castAddHom (ZMod n)).comp (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K)

end Langlands.NYLL.LocalClassFieldTheory
