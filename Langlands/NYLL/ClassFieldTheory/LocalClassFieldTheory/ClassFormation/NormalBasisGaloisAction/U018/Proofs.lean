/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.IntegerUnitMapStatements

/-!
Adapted by Worker 277 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
M145.018: Surjectivity of the integer-unit quotient map.
See the paired Markdown for source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

/-- Every quotient class of integer units has a representative. -/
theorem chosenNormalBasisIntegerUnitsQuotientMap_surjective
    (V : Subgroup 𝒪[L]ˣ) :
    chosenNormalBasisIntegerUnitsQuotientMap_surjectiveStatement L V :=
  QuotientGroup.mk'_surjective V

end

end Langlands.NYLL.LocalClassFieldTheory
