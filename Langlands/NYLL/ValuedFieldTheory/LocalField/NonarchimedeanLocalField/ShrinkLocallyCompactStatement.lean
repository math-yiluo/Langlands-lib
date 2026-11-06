/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 1782 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709:
package the local-compactness theorem signature as a universal Prop target in
Langlands.NYLL, using the published smallness theorem locally and Mathlib's
transported Shrink topology. The source proof is reserved for a separate unit.
The original license and notice are retained in licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SmallProof
import Mathlib.Topology.Instances.Shrink

/-!
# Local compactness of the universe-zero representative: statement

The target retains the supplied local-field structures and uses Mathlib's
topology on `Shrink.{0} K`, with smallness supplied locally.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The universe-zero representative of every nonarchimedean local field is
locally compact for the transported topology. This definition states the
universal target; it does not prove it. -/
def shrinkLocalField_locallyCompactStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    letI : Small.{0} K := nonarchimedeanLocalField_small K
    LocallyCompactSpace (Shrink.{0} K)

end Langlands.NYLL.LocalFieldTheory
