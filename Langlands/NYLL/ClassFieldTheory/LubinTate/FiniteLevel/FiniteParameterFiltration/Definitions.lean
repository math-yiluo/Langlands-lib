/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299, 2026-11-13: extract the indicated units from NYLL
at pinned commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the
namespace with Langlands.NYLL and use focused shared-interface imports.
See the paired Markdown for the extraction and target/proof split.
License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.Definitions

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable {K : Type u} [Field K]

/-- The image of the `k`-th higher principal-unit group in the finite
parameter quotient at primitive level `n + 1`. -/
def standardLubinTateUnitParameterSubgroup
    (F : LocalField.{u, v} K) (n k : ℕ) :
    Subgroup (standardLubinTateUnitParameter F n) :=
  Subgroup.map (standardLubinTateUnitParameterClass F n)
    (higherPrincipalUnitGroup F.toCompleteDVF k)

end Langlands.NYLL.LubinTate
