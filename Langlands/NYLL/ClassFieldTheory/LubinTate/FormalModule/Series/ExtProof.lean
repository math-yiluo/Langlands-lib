/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 462, 2026-11-14: extract only the proof of M336.002 with
its source docstring and ext attribute from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, replace the original imports by the published exact target
module, add a complete-declaration check against that target, and focus the
module documentation. The theorem name, binders, conclusion and proof are
unchanged. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.ExtStatement

/-!
# Extensionality for Lubin--Tate series

This module proves the published target
`Langlands.NYLL.LubinTate.LubinTateSeries.extStatement` (NYLL M336.002)
as the source-named theorem `Langlands.NYLL.LubinTate.LubinTateSeries.ext`,
which carries the source `@[ext]` attribute.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

namespace LubinTateSeries

variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

/-- Two Lubin--Tate series are equal when their underlying power series
are equal. -/
@[ext]
theorem ext {e e' : LubinTateSeries F π}
    (h : e.toPowerSeries = e'.toPowerSeries) : e = e' := by
  cases e
  cases e'
  cases h
  rfl

/-- The unapplied theorem has exactly the complete type of the published
target `extStatement`, which unfolds to the stated equality. -/
example : ∀ {K : Type u} [Field K] {F : LocalField.{u, v} K}
    {π : F.valuationSubring} {e e' : LubinTateSeries F π}
    (h : e.toPowerSeries = e'.toPowerSeries), extStatement h :=
  @ext

end LubinTateSeries

end Langlands.NYLL.LubinTate

end
