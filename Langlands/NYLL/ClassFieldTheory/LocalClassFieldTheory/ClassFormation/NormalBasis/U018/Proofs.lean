/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.CoordinateQuotientStatement

/-!
Adapted by Worker 277 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
M152.018: Evaluation of the coordinate quotient equivalence.
See the paired Markdown for source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L]

/-- The coordinate quotient equivalence sends a representative to its pointwise residue classes. -/
@[simp]
theorem chosenNormalBasisCoordinateQuotPiLinearEquiv_mk
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (f : Gal(L/K) → 𝒪[K]) :
    chosenNormalBasisCoordinateQuotPiLinearEquiv_mkStatement K L f :=
  rfl

end

end Langlands.NYLL.LocalClassFieldTheory
