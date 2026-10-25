/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 100, with Worker 29's source extraction and import analysis:
move the private towerLowerEmbedding to Langlands.NYLL.PortInternal.M262.d004,
split out this single definition, and reduce imports to Mathlib.FieldTheory.IsSepClosed.
The original telescope and composition are unchanged.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.IsSepClosed

/-!
# Compatible lower embedding in a field tower

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
GeneralTowerNaturality.lean, lines 44–51 (inventory M262.004).
-/

noncomputable section

namespace Langlands.NYLL.PortInternal.M262

/-- Restrict the supplied upper embedding along the tower algebra map. -/
def d004
    (K E L : Type)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L]
    (iL : L →ₐ[K] SeparableClosure K) :
    E →ₐ[K] SeparableClosure K :=
  iL.comp (IsScalarTower.toAlgHom K E L)

end Langlands.NYLL.PortInternal.M262
