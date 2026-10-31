/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 31 October 2026:
Extract M093.014 from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/
NormQuotient.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix, import only the published U013 Proofs
module and omit all other declarations. Preserve both independent universes,
the source telescope, docstring and canonical first-isomorphism body unchanged.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U013.Proofs

/-!
# First isomorphism theorem for the norm quotient

A surjective homomorphism with the actual norm subgroup as its kernel
canonically identifies the norm quotient with its target group.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u v

/-- First isomorphism theorem with an opaque norm quotient as its source. -/
def normQuotientEquivOfSurjective
    {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (hf : Function.Surjective f)
    (hker : f.ker = localNormSubgroup K L) : NormQuotient K L ≃* M := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* M
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

end

end Langlands.NYLL.LocalFieldTheory
