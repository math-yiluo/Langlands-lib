/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 30, 13 November 2026: extracted the private source theorem
LocalClassFieldTheory.towerEmbeddedFieldRange_le (inventory M262.006) as the public
Prop-valued target Langlands.NYLL.PortInternal.M262.d006Statement. The source's
private towerLowerEmbedding is the published Langlands.NYLL.PortInternal.M262.d004.
The source proof is omitted. The telescope is unchanged; the only import is the
published M262.004 definition module.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality.U004.Definitions

/-!
# Field range of the compatible lower embedding: statement target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GeneralTowerNaturality.lean`,
lines 66–73 (inventory M262.006).
-/

noncomputable section

namespace Langlands.NYLL.PortInternal.M262

/-- The image of the lower field under the restricted embedding `d004 K E L iL`
is contained in the image of the upper field under `iL`. -/
def d006Statement
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (iL : L →ₐ[K] SeparableClosure K) : Prop :=
  AlgHom.fieldRange (d004 K E L iL) ≤
    AlgHom.fieldRange iL

end Langlands.NYLL.PortInternal.M262
