/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions

/-!
# Finiteness of concrete principal-unit subquotients (target)

Adapted by Worker 299 and Worker 476 from NYLL M231.018 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`
(`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnits/Core.lean`,
lines 340–344). Modifications: add the `Langlands.NYLL` namespace prefix,
isolate the proposition as a `Prop`-valued definition with suffix `Statement`,
and import only the published higher principal-unit subgroup construction.
The paired Markdown lists all modifications. The original Apache-2.0 license
and notice are retained in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

namespace DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

/-- Source M231.018: over a finite residue field, the quotient of the level-`m`
principal units by the level-`n` principal units lying in them is finite. -/
def finite_principalUnitSubquotient_of_finite_residueStatement
    {K : Type u} [Field K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
    [Finite F.residueField] (m n : ℕ) : Prop :=
  Finite (higherPrincipalUnitGroup F m ⧸
    (higherPrincipalUnitGroup F n).subgroupOf (higherPrincipalUnitGroup F m))

end DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

end Langlands.NYLL.LocalFieldTheory
