/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 319 (2026-11-14): extract M335.011 from upstream
   commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace
   with Langlands.NYLL, and replace the original whole-module imports by
   the focused integer-ring equivalence and Mathlib's unit-equivalence API.
   The original LICENSE and NOTICE remain in licenses/NYLL/. -/

import Mathlib.Algebra.Group.Units.Equiv
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.IntegerEquiv

/-!
# The canonical integer-unit equivalence

The integer-ring equivalence induces a multiplicative equivalence on units.
-/

noncomputable section

open scoped ValuativeRel

namespace Langlands.NYLL.LubinTate

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The induced multiplicative equivalence between the two valuation-ring
unit groups. -/
noncomputable def standardLocalFieldIntegerUnitsEquiv :
    𝒪[K]ˣ ≃* (standardLocalField K).valuationSubringˣ :=
  Units.mapEquiv (standardLocalFieldIntegerEquiv K).toMulEquiv

end Langlands.NYLL.LubinTate

end
