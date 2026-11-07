/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 1803 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709:
package the nontriviality theorem signature as a universal Prop target in
Langlands.NYLL, using the published smallness theorem locally and installing
the published transported valuative relation locally. The source proof is
reserved for a separate unit.
The original license and notice are retained in licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkValuativeRel

/-!
# Nontriviality of the transported valuative relation: statement

The target retains the supplied local-field structures and concerns the
published valuative relation on `Shrink.{0} K`, with smallness and the
relation supplied locally.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The valuative relation transported to the universe-zero representative of
every nonarchimedean local field is nontrivial. This definition states the
universal target; it does not prove it. -/
def shrinkLocalField_isNontrivialStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    letI : ValuativeRel (Shrink.{0} K) := shrinkLocalFieldValuativeRel K
    ValuativeRel.IsNontrivial (Shrink.{0} K)

end Langlands.NYLL.LocalFieldTheory
