/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 320, 14 November 2026:
Extract only M138.024, source lines 308–319, from
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
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Valuation.Extension

/-!
# Inertia degree and the canonical residue extension: statement

The closed proposition target for NYLL M138.024.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The mathlib inertia degree of the maximal ideals agrees with the concrete
degree of the canonical residue-field extension supplied by a valuation
extension. -/
def maximalIdeal_inertiaDeg_eq_residue_finrankStatement : Prop :=
  ∀ (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)],
    (𝓂[L] : Ideal 𝒪[L]).inertiaDeg 𝒪[K] =
      Module.finrank 𝓀[K] 𝓀[L]

end Langlands.NYLL.LocalFieldTheory
