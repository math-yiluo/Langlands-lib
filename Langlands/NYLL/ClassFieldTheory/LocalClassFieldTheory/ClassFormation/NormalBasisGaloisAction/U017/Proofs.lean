/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.IntegerUnitMapStatements

/-!
Adapted by Worker 277 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
M145.017: Injectivity of the integer-unit subgroup inclusion.
See the paired Markdown for source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

/-- The subgroup inclusion is injective. -/
theorem chosenNormalBasisPrincipalUnitSubgroupInclusion_injective
    (V : Subgroup 𝒪[L]ˣ) :
    chosenNormalBasisPrincipalUnitSubgroupInclusion_injectiveStatement L V :=
  Subtype.val_injective

end

end Langlands.NYLL.LocalClassFieldTheory
