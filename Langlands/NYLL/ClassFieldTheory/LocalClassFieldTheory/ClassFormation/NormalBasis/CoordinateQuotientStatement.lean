/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.CoordinateMaximalSubmodule
import Mathlib.NumberTheory.LocalField.Basic

/-!
Adapted by Worker 197 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
Evaluation target for the coordinate quotient equivalence
See the paired Markdown for exact source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L] [FiniteDimensional K L]

def chosenNormalBasisCoordinateQuotPiLinearEquiv_mkStatement
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (f : Gal(L/K) → 𝒪[K]) : Prop :=
chosenNormalBasisCoordinateQuotPiLinearEquiv K L
        (Submodule.Quotient.mk f) =
      fun σ : Gal(L / K) => Submodule.Quotient.mk (f σ)

end

end Langlands.NYLL.LocalClassFieldTheory
