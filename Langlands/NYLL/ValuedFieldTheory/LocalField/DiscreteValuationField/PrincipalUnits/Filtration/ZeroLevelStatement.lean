/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions

/-!
# The zero level of the principal-unit filtration

Adapted by Worker 311 from NYLL M225.008 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Modifications: add the
`Langlands.NYLL` namespace prefix, isolate the proposition as a
`Prop`-valued definition with suffix `Statement`, and import only the
higher principal-unit subgroup construction.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

namespace DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

variable {K : Type u} [Field K]

/-- Source M225.008: the zero level is the entire valuation-ring unit group. -/
def zero_eq_topStatement
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) : Prop :=
  higherPrincipalUnitGroup F 0 = ⊤

end DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

end Langlands.NYLL.LocalFieldTheory
