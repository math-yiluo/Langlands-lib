/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 134, 14 November 2026: extract the proof of M131.020 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnits.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 200–207. Add the
Langlands.NYLL namespace prefix, declare the source `lemma` as a `theorem`
whose type is the published target applied to its parameters, unfold that
target before the source tactics, and import only AntitoneQuotientStatements.
Omit the source noncomputable section and all other source declarations.
See the paired Markdown; the original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.AntitoneQuotientStatements

/-!
# A unit identity for valuation-ring units

For units `a b` of the valuation ring,
`ab - 1 = (a - 1)(b - 1) + (a - 1) + (b - 1)`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Algebra identity used to prove multiplicative closure of principal units. -/
theorem unit_mul_sub_one_eq (K : Type u) [Field K] [ValuativeRel K] (a b : 𝒪[K]ˣ) :
    unit_mul_sub_one_eqStatement K a b := by
  unfold unit_mul_sub_one_eqStatement
  simp only [Units.val_mul]
  ring

end Langlands.NYLL.LocalFieldTheory
