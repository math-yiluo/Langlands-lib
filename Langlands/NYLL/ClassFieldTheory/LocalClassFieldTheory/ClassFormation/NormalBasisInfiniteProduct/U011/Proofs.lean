/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.CorrectionProductStatements

/-!
Adapted by Worker 277 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
M150.011: Successor equation for normal-basis correction products.
See the paired Markdown for source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

/-- A successor product appends the correction at the preceding index. -/
@[simp]
theorem chosenNormalBasisPrincipalUnitCorrectionProduct_succ
    (z : Nat → 𝒪[L]ˣ) (d : Nat) :
    chosenNormalBasisPrincipalUnitCorrectionProduct_succStatement L z d :=
  rfl

end

end Langlands.NYLL.LocalClassFieldTheory
