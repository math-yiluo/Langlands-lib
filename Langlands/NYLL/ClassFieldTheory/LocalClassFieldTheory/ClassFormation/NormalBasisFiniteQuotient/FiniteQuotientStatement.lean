/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions
import Mathlib.NumberTheory.LocalField.Basic

/-!
Adapted by Worker 197 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
Finiteness target for quotients containing a principal-unit level
See the paired Markdown for exact source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open LocalFieldTheory

variable (L : Type u) [Field L] [ValuativeRel L]

def finite_chosenNormalBasisIntegerUnitsQuotient_of_principalUnits_leStatement
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (m : Nat) (V : Subgroup 𝒪[L]ˣ) (h : principalUnits L m ≤ V) : Prop :=
Finite (𝒪[L]ˣ ⧸ V)

end

end Langlands.NYLL.LocalClassFieldTheory
