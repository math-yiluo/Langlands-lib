/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 89, 13 November 2026: the proof of the private source theorem
LocalClassFieldTheory.towerEmbeddedFieldRange_le (inventory M262.006), stated as
Langlands.NYLL.PortInternal.M262.d006 for the published target
Langlands.NYLL.PortInternal.M262.d006Statement. The telescope and tactic proof are
unchanged; the conclusion is the published target applied to the telescope, and
the private towerLowerEmbedding is the published Langlands.NYLL.PortInternal.M262.d004.
Prepared by Worker 294, 13 November 2026, from Worker 89's shared draft:
verified against the pinned original and the published target; no proof changes.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality.U006.Statements

/-!
# Field range of the compatible lower embedding: proof

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GeneralTowerNaturality.lean`,
lines 66–76 (inventory M262.006).
-/

noncomputable section

namespace Langlands.NYLL.PortInternal.M262

/-- The image of the lower field under the restricted embedding `d004 K E L iL`
is contained in the image of the upper field under `iL`. -/
theorem d006
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (iL : L →ₐ[K] SeparableClosure K) :
    d006Statement K E L iL := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨algebraMap E L y, rfl⟩

end Langlands.NYLL.PortInternal.M262
