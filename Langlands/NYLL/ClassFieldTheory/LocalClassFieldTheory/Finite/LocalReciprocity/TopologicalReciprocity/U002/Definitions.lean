/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 10 November 2026: extract M257.002–003 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Give the source-private
helpers stable PortInternal names, use published focused imports and qualify
references. Preserve the common universe and all parameters and bodies.
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions

/-! # Integer-unit norm and its image subgroup -/

noncomputable section

universe u

namespace Langlands.NYLL.PortInternal.M257

open scoped ValuativeRel

/-- The norm map restricted to valuation-ring units upstairs. -/
def d002
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel L] : 𝒪[L]ˣ →* Kˣ :=
  (Langlands.NYLL.LocalFieldTheory.normUnits K L).comp
    (Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits L)

/-- The image of valuation-ring units under the field norm. -/
def d003
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel L] : Subgroup Kˣ :=
  MonoidHom.range (d002 K L)

end Langlands.NYLL.PortInternal.M257
