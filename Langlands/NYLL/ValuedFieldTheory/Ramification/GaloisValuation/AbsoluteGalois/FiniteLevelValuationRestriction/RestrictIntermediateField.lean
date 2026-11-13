/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 122 (2026-11-13): extract only the definition
   M233.004, RamificationTheory.ValuationSubring.restrictIntermediateField
   (FiniteLevelValuationRestriction.lean, lines 110-118, with the ambient
   namespace, noncomputable section and universes at lines 53, 60, 62 and
   64), from upstream commit fbd320cd8b1b06487c58227e92eb135794267709.
   Prefix the namespace with Langlands.NYLL, keep only the section variables
   the definition uses, and replace the 38 upstream imports by two focused
   Mathlib imports. The original LICENSE and NOTICE are retained in
   licenses/NYLL/. -/

import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Restricting a valuation subring to an intermediate field

The restriction of a valuation subring `A` of an ambient field `Ω` to an
intermediate field `E` of `Ω / K` is the preimage of `A` under the inclusion
`E → Ω`.
-/

namespace Langlands.NYLL.RamificationTheory

noncomputable section

universe u v

namespace ValuationSubring

section RestrictIntermediateField

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

/-- Restrict a valuation subring of an ambient field to an intermediate field. -/
def restrictIntermediateField
    (A : ValuationSubring Ω) (E : IntermediateField K Ω) :
    ValuationSubring E :=
  A.comap (algebraMap E Ω)

end RestrictIntermediateField

end ValuationSubring

end

end Langlands.NYLL.RamificationTheory
