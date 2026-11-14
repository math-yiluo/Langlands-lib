/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 320, 14 November 2026:
Extract only M161.002, source lines 46–55, from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix the source namespace with
Langlands.NYLL and append Statement to the theorem name. Package its complete
type as a closed Prop-valued definition, preserving the source universe,
parameter and instance binder order, and conclusion; omit the proof. Replace
the source imports by the focused dependencies below and omit the unnecessary
noncomputable section. See the paired Markdown for the complete change record.
The retained Apache-2.0 license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.Definitions

/-!
# Ramification index of an unramified valued extension: statement

The closed proposition target for NYLL M161.002.
-/

namespace Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

universe u

open scoped ValuativeRel

/-- An unramified valued extension has ramification index one. -/
def unramifiedValuation_ramificationIdx_eq_oneStatement : Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] [IsUnramifiedValuedExtension K L],
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1

end Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField
