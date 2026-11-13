/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only M283.002 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and preserve the source telescope, docstring and body, which chooses
a witness of the published theorem exists_valuationOne_unit_of_ringEquiv.
Replace the source imports by the single published module proving that
theorem. Omit the namespace openings and all other declarations of the
module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U001.Proofs

/-!
# A chosen valuation-one unit transported by a ring equivalence

A unit of a nonarchimedean local field, chosen once and for all, whose
normalized valuation is one and whose image under a valuation-compatible
ring equivalence also has normalized valuation one.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

/-- A chosen valuation-one unit whose image under a valuation-compatible
ring equivalence also has valuation one. -/
noncomputable def chosenValuationOneUnitOfRingEquiv
    (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) :
    Lˣ :=
  Classical.choose
    (exists_valuationOne_unit_of_ringEquiv L M phi hmem)

end

end Langlands.NYLL.LocalClassFieldTheory
