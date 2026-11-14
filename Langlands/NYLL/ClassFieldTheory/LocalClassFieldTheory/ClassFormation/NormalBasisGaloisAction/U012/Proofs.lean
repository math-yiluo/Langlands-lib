/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.IntegerUnitMapStatements

/-!
Adapted by Worker 277 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
M145.012: Evaluation of the integer-unit subgroup inclusion.
See the paired Markdown for source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

/-- The inclusion evaluates to the underlying integer unit. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitSubgroupInclusion_apply
    (V : Subgroup 𝒪[L]ˣ) (a : V) :
    chosenNormalBasisPrincipalUnitSubgroupInclusion_applyStatement L V a :=
  rfl

end

end Langlands.NYLL.LocalClassFieldTheory
