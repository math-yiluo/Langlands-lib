/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 1686 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709:
M422.003 is isolated in Langlands.NYLL with explicit binders. The private
smallness wrapper is replaced by local use of the published smallness
theorem, and the published Shrink valuation is imported and reused.
The definition retains instance_reducible and explicit noncomputable status.
The original license and notice are retained in licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkValuation

/-!
# The valuative relation on the universe-zero representative of a local field

Apply Mathlib's `ValuativeRel.ofValuation` to the published valuation on
`Shrink.{0} K`. The resulting data can be installed locally as an instance.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The valuative relation induced by the canonical valuation pulled back to
`Shrink.{0} K`. Smallness is supplied locally by the published theorem
`nonarchimedeanLocalField_small`. -/
@[instance_reducible]
noncomputable def shrinkLocalFieldValuativeRel (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    ValuativeRel (Shrink.{0} K) :=
  letI : Small.{0} K := nonarchimedeanLocalField_small K
  ValuativeRel.ofValuation (shrinkLocalFieldValuation K)

end Langlands.NYLL.LocalFieldTheory
