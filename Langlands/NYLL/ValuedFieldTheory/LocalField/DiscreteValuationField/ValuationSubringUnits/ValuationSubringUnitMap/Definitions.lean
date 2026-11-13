/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 324, 2026-11-13: extract only M388.001, lines 31–34,
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify
the namespace with Langlands.NYLL, explicitly qualify the existing
CompleteDVF argument type, and replace the source Basic import with the
published Complete.Projections module. The definition body is unchanged.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections

/-!
# Valuation-subring units inside field units

The canonical homomorphism from the units of a chosen complete-DVF
valuation subring to the units of its underlying field.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable {K : Type u} [Field K]

/-- The inclusion `O_K^* -> K^*` for the chosen valuation ring of a complete
DVF. -/
noncomputable def valuationSubringUnitsToFieldUnits
    (F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) :
    F.valuationSubringˣ →* Kˣ :=
  F.valuation.valuationSubring.unitGroup.subtype.comp
    F.valuation.valuationSubring.unitGroupMulEquiv.symm.toMonoidHom

end Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF

end
