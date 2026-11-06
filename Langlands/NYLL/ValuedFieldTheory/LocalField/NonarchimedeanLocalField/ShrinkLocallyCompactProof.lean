/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 1782 from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709:
prove the published universal target in Langlands.NYLL, importing its statement
and installing the published smallness theorem locally. The original proof
transfers local compactness along the inverse Shrink homeomorphism.
The original license and notice are retained in licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkLocallyCompactStatement

/-!
# Local compactness of the universe-zero representative: proof

The supplied topology on a nonarchimedean local field is locally compact.
The inverse Shrink homeomorphism transfers this to its small representative.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The universe-zero representative of every nonarchimedean local field is
locally compact for Mathlib's transported topology. -/
theorem shrinkLocalField_locallyCompact :
    shrinkLocalField_locallyCompactStatement.{u} := by
  intro K _ _ _ _
  let : Small.{0} K := nonarchimedeanLocalField_small K
  exact (Shrink.homeomorph K).symm.isOpenEmbedding.locallyCompactSpace

end Langlands.NYLL.LocalFieldTheory
