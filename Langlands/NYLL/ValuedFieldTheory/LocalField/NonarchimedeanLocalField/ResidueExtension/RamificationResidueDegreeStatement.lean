/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 320, 14 November 2026:
Extract only M138.029, source lines 382–395, from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix the source namespace with
Langlands.NYLL and append Statement to the theorem name. Package its complete
type as a closed Prop-valued definition, preserving the source universe,
parameter and instance binder order, and conclusion; omit the proof. Replace
the source imports by the focused dependencies below and omit the unnecessary
noncomputable section. See the paired Markdown for the complete change record.
The retained Apache-2.0 license and notices are in licenses/NYLL/.
-/

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Valuation.Extension

/-!
# Ramification index times the canonical residue degree: statement

The closed proposition target for NYLL M138.029.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The local ramification identity with the inertia degree rewritten as the
finite-dimensional degree of the canonical residue-field extension. -/
def maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrankStatement : Prop :=
  ∀ (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]],
    Ideal.ramificationIdx' (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L]) *
      Module.finrank 𝓀[K] 𝓀[L] =
        Module.finrank K L

end Langlands.NYLL.LocalFieldTheory
