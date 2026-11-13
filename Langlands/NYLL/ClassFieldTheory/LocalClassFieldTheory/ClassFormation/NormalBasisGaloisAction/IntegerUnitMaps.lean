/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
Adapted by Worker 197 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
The integer-unit subgroup inclusion and quotient projection
See the paired Markdown for exact source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

def chosenNormalBasisPrincipalUnitSubgroupInclusion
    (V : Subgroup 𝒪[L]ˣ) : V →* 𝒪[L]ˣ :=
  V.subtype

def chosenNormalBasisIntegerUnitsQuotientMap
    (V : Subgroup 𝒪[L]ˣ) : 𝒪[L]ˣ →* (𝒪[L]ˣ ⧸ V) :=
  QuotientGroup.mk' V

end

end Langlands.NYLL.LocalClassFieldTheory
