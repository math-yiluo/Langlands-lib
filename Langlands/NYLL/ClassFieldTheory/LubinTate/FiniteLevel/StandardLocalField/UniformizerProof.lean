/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 212 on 2026-11-16: extract the proof of M335.021
from StandardLocalField.lean at fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, replace the six source imports
by the published exact target and chosen-prime irreducibility proof,
retain only the used opened namespace, and state the theorem using the
fully applied target, unfolded before the unchanged source proof.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.UniformizerStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U005.Proofs

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The transported canonical prime element is a uniformizer for the
valuation in the standard local-field package. -/
theorem standardLocalFieldUniformizer_isUniformizer :
    standardLocalFieldUniformizer_isUniformizerStatement K := by
  unfold standardLocalFieldUniformizer_isUniformizerStatement
  have hirr :
      Irreducible (standardLocalFieldUniformizer K) :=
    (chosenIntegerRingUniformizer_irreducible K).map
      (standardLocalFieldIntegerEquiv K)
  exact
    Valuation.isUniformizer_of_maximalIdeal_eq_span
      (v := (standardLocalField K).valuation)
      hirr.maximalIdeal_eq

end Langlands.NYLL.LubinTate
