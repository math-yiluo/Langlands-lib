/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 134, 14 November 2026: extract the proof of M131.005 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 79–85. Add the
Langlands.NYLL namespace prefix, give the theorem the published target
applied to its parameters as its type and import only
AntitoneQuotientStatements. The source tactic proof is unchanged. Omit the
source noncomputable section and all other source declarations. See the
paired Markdown; the original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.AntitoneQuotientStatements

/-!
# Antitonicity of the principal-unit filtration

For `m ≤ n`, the `n`-th principal-unit group `U^n` is contained in `U^m`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Principal-unit groups decrease as the filtration index increases. -/
theorem principalUnits_antitone (K : Type u) [Field K] [ValuativeRel K]
    {m n : Nat} (h : m ≤ n) :
    principalUnits_antitoneStatement K h := by
  intro u hu
  exact Ideal.pow_le_pow_right h hu

end Langlands.NYLL.LocalFieldTheory
