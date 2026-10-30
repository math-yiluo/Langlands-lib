/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 29 October 2026:
Extract M093.007 from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/
NormQuotient.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix, import the published U006 Proofs
module alone, omit all other declarations, and preserve the source telescope,
universes u and v, docstring and definition body.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U006.Proofs

/-!
# Homomorphisms descended through the general norm quotient

A homomorphism on base-field units that kills every norm induces a
homomorphism on the named norm quotient.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u v

/-- Define a homomorphism out of a norm quotient from a homomorphism on
`Kˣ` that kills every local norm. -/
def normQuotientLift {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L]
    [Group M] (f : Kˣ →* M) (h : localNormSubgroup K L ≤ f.ker) :
    NormQuotient K L →* M := by
  change (Kˣ ⧸ localNormSubgroup K L) →* M
  let N := localNormSubgroup K L
  exact QuotientGroup.lift N f h

end

end Langlands.NYLL.LocalFieldTheory
