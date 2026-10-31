/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 30 October 2026:
Extract M093.012 from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/
NormQuotient.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix, import only the published U011 Proofs
module, omit the unused universe v and all other declarations, and retain the
source telescope, docstring and definition body unchanged.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U011.Proofs

/-!
# Equal norm subgroups identify norm quotients

The canonical multiplicative equivalence between the two norm quotients over
the same base field when their actual norm subgroups agree.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

/-- Identify two norm quotients when their defining norm subgroups agree. -/
def normQuotientEquivOfNormSubgroupEq
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M) :
    NormQuotient K L ≃* NormQuotient K M := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* (Kˣ ⧸ localNormSubgroup K M)
  exact QuotientGroup.quotientMulEquivOfEq h

end

end Langlands.NYLL.LocalFieldTheory
