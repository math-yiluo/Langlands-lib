/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 10 November 2026: focused extraction from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnitTopology.lean at fbd320cd8b1b06487c58227e92eb135794267709;
add Langlands.NYLL to the namespace and replace the full NYLL import by
its published focused prerequisite. Retain source parameters and construction.
LICENSE and NOTICE: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions

/-! # The subgroup of valuation-integer units -/

noncomputable section

universe u

namespace Langlands.NYLL.LocalFieldTheory

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The image of valuation-ring units in the field unit group. -/
def localBaseUnitSubgroup
    (K : Type u) [Field K] [ValuativeRel K] : Subgroup Kˣ :=
  MonoidHom.range (integerUnitsToFieldUnits K)

end Langlands.NYLL.LocalFieldTheory
