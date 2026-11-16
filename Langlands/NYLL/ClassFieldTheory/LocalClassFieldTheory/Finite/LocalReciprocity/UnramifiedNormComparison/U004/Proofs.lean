/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 205, 2026-11-16: extract M267.004, lines 81–92,
from Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace
with Langlands.NYLL and prove the focused closed proposition target,
introducing its unchanged Type-0 source telescope. Replace the source M266.014 projection-surjectivity wrapper by Mathlib QuotientGroup.mk'_surjective; retain the same lifted-map proof.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.U004.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U009.Proofs

/-! # NYLL M267.004: canonical comparison proof -/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- Every unramified valuation class is represented by an actual norm quotient class. -/
theorem normQuotientToUnramifiedNormQuotient_surjective :
    normQuotientToUnramifiedNormQuotient_surjectiveStatement := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact normQuotientLift_surjective
    (unramifiedNormClass K (Module.finrank K L))
    (by
      intro x hx
      rw [MonoidHom.mem_ker]
      exact (unramifiedNormClass_eq_one_iff_mem K (Module.finrank K L) x).2
        (localNormSubgroup_le_unramifiedNormSubgroup K L hx))
    (QuotientGroup.mk'_surjective
      (unramifiedNormSubgroup K (Module.finrank K L)))

end Langlands.NYLL.LocalClassFieldTheory
