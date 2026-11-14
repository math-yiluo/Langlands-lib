/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Prove the published closed form of M283.003 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean at
fbd320cd8b1b06487c58227e92eb135794267709 under the source theorem name with
the Langlands.NYLL namespace prefix. Keep the original proof term, applied
after introducing the binders of the closed statement. Import only the
published M283.003/004 Statements module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
Worker 602, 14 November 2026: reuse Worker 56's shared proof draft;
verify the original correspondence and correct the paired documentation.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U003.Statements

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The chosen transported unit has valuation one in its source field. -/
theorem chosenValuationOneUnitOfRingEquiv_source :
    chosenValuationOneUnitOfRingEquiv_sourceStatement := by
  intro L M _ _ _ _ _ _ _ _ phi hmem
  exact
    (Classical.choose_spec
      (exists_valuationOne_unit_of_ringEquiv L M phi hmem)).1

end Langlands.NYLL.LocalClassFieldTheory
