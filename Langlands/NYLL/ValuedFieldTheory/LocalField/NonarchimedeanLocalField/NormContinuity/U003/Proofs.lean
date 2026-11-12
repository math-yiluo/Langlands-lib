/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 202, 12 November 2026: extract M255.003 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormContinuity.lean
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and import the published focused Statement target. Preserve
the original parameters and units_map proof; add a change step for the target.
LICENSE and NOTICE are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity.U003.Statements

/-! # Continuity of the valuation-integer unit inclusion -/

universe u

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The canonical inclusion from valuation-integer units to field units is continuous. -/
theorem integerUnitsToFieldUnits_continuous
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] :
    integerUnitsToFieldUnits_continuousStatement K := by
  change Continuous (integerUnitsToFieldUnits K)
  unfold IsNonarchimedeanLocalField.integerUnitsToFieldUnits
  exact Continuous.units_map
    ((algebraMap 𝒪[K] K).toMonoidHom) continuous_subtype_val

end Langlands.NYLL.LocalFieldTheory
