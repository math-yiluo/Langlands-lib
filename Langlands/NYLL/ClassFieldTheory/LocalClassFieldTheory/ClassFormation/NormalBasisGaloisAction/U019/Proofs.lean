/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.IntegerUnitMapStatements

/-!
Adapted by Worker 277 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
M145.019: Exactness at the integer-unit group.
See the paired Markdown for source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

/-- The inclusion's range is the quotient projection's kernel. -/
theorem chosenNormalBasisPrincipalUnitSubgroupInclusion_range_eq_ker_quotient
    (V : Subgroup 𝒪[L]ˣ) :
    chosenNormalBasisPrincipalUnitSubgroupInclusion_range_eq_ker_quotientStatement L V := by
  ext a
  change (∃ v : V, (v : 𝒪[L]ˣ) = a) ↔ QuotientGroup.mk' V a = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨v, rfl⟩
    exact v.2
  · intro ha
    exact ⟨⟨a, ha⟩, rfl⟩

end

end Langlands.NYLL.LocalClassFieldTheory
