/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 319, 2026-11-16: extract only the proof of M335.017
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix
the namespace with Langlands.NYLL; replace the source imports by the
published comparison statements and the higher-principal-unit comparison
proof; state the theorem with the fully applied imported target and unfold
it before the original proof. Replace the module documentation.
The original license and notices are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.PrincipalUnitComparisonStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.HigherPrincipalUnitsComparisonProof

/-!
# Comparison of packaged and topology-first field principal units

Mapping the packaged higher principal-unit subgroup into the field's units
gives the topology-first field principal-unit subgroup.
-/

noncomputable section

open scoped ValuativeRel

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The packaged higher principal-unit subgroup maps exactly to the
topology-first field principal-unit subgroup. -/
theorem standardLocalFieldHigherPrincipalUnitGroup_map_eq_fieldPrincipalUnits
    (n : ℕ) :
    standardLocalFieldHigherPrincipalUnitGroup_map_eq_fieldPrincipalUnitsStatement K n := by
  unfold standardLocalFieldHigherPrincipalUnitGroup_map_eq_fieldPrincipalUnitsStatement
  change
    (higherPrincipalUnitGroup
        (standardLocalField K).toCompleteDVF n).map
        ((integerUnitsToFieldUnits K).comp
          (standardLocalFieldIntegerUnitsEquiv K).symm.toMonoidHom) =
      (principalUnits K n).map (integerUnitsToFieldUnits K)
  rw [← Subgroup.map_map,
    standardLocalFieldHigherPrincipalUnitGroup_map_eq_principalUnits]

end Langlands.NYLL.LubinTate

end
