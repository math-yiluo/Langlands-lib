/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 120, 14 November 2026: extract the proof of M140.010 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/Valuation.lean,
lines 206-220, at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix
the namespace with Langlands.NYLL, import only the published Valuation
Statements module, and prove the published target applied to all its
parameters; the original change is preceded by unfolding the target
proposition. Omit the source noncomputable section and all other source
declarations. See the paired Markdown; the original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.Statements

/-!
# Valuation one versus valuation zero

For a field unit, the multiplicative normalized valuation is `1` exactly when
the additive normalized valuation is `0`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

universe u

open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- Multiplicative and additive presentations of valuation-one/valuation-zero
agree for a field unit. -/
theorem valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zero
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] (x : Lˣ) :
    valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zeroStatement L x := by
  unfold valuationUnitsMulHom_eq_one_iff_valuationMap_eq_zeroStatement
  change valuationUnitsMulHom L x = 1 ↔
    Multiplicative.toAdd (valuationUnitsMulHom L x) = 0
  constructor
  · intro hx
    exact congrArg Multiplicative.toAdd hx
  · intro hx
    apply Multiplicative.toAdd.injective
    exact hx

end Langlands.NYLL.LocalClassFieldTheory
