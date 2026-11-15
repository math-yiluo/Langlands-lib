/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 415, 2026-11-14: extract only the statements of M335.014
(lines 204–209) and M335.017 (lines 248–253) from
Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean at
pinned commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the
namespace with Langlands.NYLL; replace each theorem by a Prop-valued
definition with the `Statement` suffix and omit its proof; replace the
source imports by focused imports of the published declarations used.
See the paired Markdown. License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.IntegerUnitsEquiv
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.ValuationUnitsToFieldUnits
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.Definitions

/-!
# Principal-unit comparison targets for the standard local field

The packaged higher principal-unit subgroup of `standardLocalField K`,
mapped back through the canonical integer-unit equivalence, is the
topology-first principal-unit subgroup; mapped into `Kˣ`, it is the
topology-first field principal-unit subgroup. This module states both
comparisons and proves neither.
-/

noncomputable section

open scoped ValuativeRel

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Mapping packaged higher principal units back through the canonical
integer-unit equivalence gives the topology-first principal-unit subgroup. -/
def standardLocalFieldHigherPrincipalUnitGroup_map_eq_principalUnitsStatement
    (n : ℕ) : Prop :=
  (higherPrincipalUnitGroup
      (standardLocalField K).toCompleteDVF n).map
      (standardLocalFieldIntegerUnitsEquiv K).symm.toMonoidHom =
    principalUnits K n

/-- The packaged higher principal-unit subgroup maps exactly to the
topology-first field principal-unit subgroup. -/
def standardLocalFieldHigherPrincipalUnitGroup_map_eq_fieldPrincipalUnitsStatement
    (n : ℕ) : Prop :=
  (higherPrincipalUnitGroup
      (standardLocalField K).toCompleteDVF n).map
      (standardLocalFieldValuationUnitsToFieldUnits K) =
    LocalFieldTheory.fieldPrincipalUnits K n

end Langlands.NYLL.LubinTate

end
