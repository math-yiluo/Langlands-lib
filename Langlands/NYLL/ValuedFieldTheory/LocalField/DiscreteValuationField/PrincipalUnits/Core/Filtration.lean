/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299, 2026-11-13: extract M231.020 at pinned commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL, and prove the structure's antitone law directly with
Mathlib's Ideal.pow_le_pow_right. Import only the shared concrete subgroup
and abstract filtration definitions. License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Filtration

noncomputable section

universe u v

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

variable {K : Type u} [Field K]
variable (F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The concrete principal-unit filtration as the abstract filtration API. -/
def toPrincipalUnitFiltration : AntitoneSubgroupFiltration F.valuationSubringˣ where
  subgroup := higherPrincipalUnitGroup F
  antitone := by
    intro m n h a ha
    exact (Ideal.pow_le_pow_right h) ha

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
