/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 212 on 2026-11-16: extract only the assertion of M377.002
from StandardSubgroupIndex.lean at fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, replace the six original imports
by the three focused published modules below, retain only the used opened
namespace, and package the theorem type as a Prop-valued definition with
the Statement suffix. Omit the source proof and all other source units.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.UniformizerProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup.BaseUniformizerUnit.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The inverse of the canonical packaged Lubin--Tate uniformizer has
positive normalized additive valuation. -/
def standardLubinTateCanonicalBaseUniformizerUnit_inv_valuationMapStatement : Prop :=
  valuationMap K
      (Additive.ofMul
        (standardLubinTateBaseUniformizerUnit
          (standardLocalFieldUniformizer_isUniformizer K))⁻¹) =
    1

end Langlands.NYLL.LubinTate
