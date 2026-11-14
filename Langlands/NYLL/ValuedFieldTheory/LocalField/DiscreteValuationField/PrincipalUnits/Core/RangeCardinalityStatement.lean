/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions

/-!
# The cardinality of the principal-unit range `U^1/U^n`

Adapted by Worker 438 from NYLL M231.064 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Modifications: add the
`Langlands.NYLL` namespace prefix, isolate the proposition as a
`Prop`-valued definition with suffix `Statement`, and import only the
higher principal-unit subgroup construction.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

namespace DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

variable {K : Type u} [Field K]

set_option linter.unusedVariables false in
/-- Source M231.064: for a complete discrete valuation field with finite residue
field `k`, a uniformizer `pi` and `1 ≤ n`, the quotient `U^1/U^n` of the first
principal-unit group by the `n`-th one has `|k| ^ (n - 1)` elements. -/
def card_principalUnitSubquotient_one_eq_residue_pow_of_uniformizerStatement
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    [Finite F.residueField]
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K))
    {n : ℕ} (hn : 1 ≤ n) : Prop :=
  Nat.card (higherPrincipalUnitGroup F 1 ⧸
      (higherPrincipalUnitGroup F n).subgroupOf
        (higherPrincipalUnitGroup F 1)) =
    Nat.card F.residueField ^ (n - 1)

end DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

end Langlands.NYLL.LocalFieldTheory
