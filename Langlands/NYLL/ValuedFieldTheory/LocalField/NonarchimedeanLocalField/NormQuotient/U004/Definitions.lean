/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 29 October 2026:
Extract M093.004 from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/
NormQuotient.lean at fbd320cd8b1b06487c58227e92eb135794267709.
Add the Langlands.NYLL namespace prefix, import the published normQuotientCommGroup
instance alone, omit the unused universe v and all other declarations,
and preserve the source telescope, docstring and definition body.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U003.Definitions

/-!
# The concrete representation of the general norm quotient

The multiplicative equivalence from the named norm quotient to the concrete
quotient of base-field units by the local norm subgroup.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

/-- The explicit boundary to the concrete quotient implementation.  Clients
that need quotient-level constructions should use this equivalence instead of
unfolding `NormQuotient`. -/
def normQuotientConcreteEquiv
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    NormQuotient K L ≃* Kˣ ⧸ localNormSubgroup K L := by
  change (Kˣ ⧸ localNormSubgroup K L) ≃* Kˣ ⧸ localNormSubgroup K L
  exact MulEquiv.refl _

end

end Langlands.NYLL.LocalFieldTheory
