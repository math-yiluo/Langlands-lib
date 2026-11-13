/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.LocalField.Basic

/-!
Adapted by Worker 197 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
Continuity target for integer-ring automorphisms
See the paired Markdown for exact source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

def continuous_integerRingEquiv_of_isNonarchimedeanLocalFieldStatement
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    (e : 𝒪[L] ≃+* 𝒪[L]) : Prop :=
Continuous e

end

end Langlands.NYLL.LocalClassFieldTheory
