/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the asserted types of M283.003
chosenValuationOneUnitOfRingEquiv_source and M283.004
chosenValuationOneUnitOfRingEquiv_target from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and package all eleven original binders of each theorem inside a
closed Prop-valued definition with the suffix Statement, preserving their
order, binder kinds and the source's universe-zero field types. The named
hypothesis hmem stays named, because the conclusion mentions it.
Write the published normalized valuation map by its full name instead of
using the source namespace openings, and replace the source imports by the
single published module defining chosenValuationOneUnitOfRingEquiv. Defer
the truth proofs; install no instance or simp registration. Omit the
original noncomputable section and all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.AmbientPrimeNormTransport.U002.Definitions

/-!
# The chosen transported unit has valuation one: statements

Closed propositions saying that the chosen unit
`chosenValuationOneUnitOfRingEquiv L M phi hmem` has normalized valuation
one in `L`, and that its image under `phi` has normalized valuation one in
`M`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The chosen transported unit has valuation one in its source field. -/
def chosenValuationOneUnitOfRingEquiv_sourceStatement : Prop :=
  ∀ (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring),
    Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap L
        (Additive.ofMul
          (chosenValuationOneUnitOfRingEquiv L M phi hmem)) = 1

/-- The image of the chosen transported unit has valuation one in the
target field. -/
def chosenValuationOneUnitOfRingEquiv_targetStatement : Prop :=
  ∀ (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M)
    (hmem : ∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring),
    Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap M
        (Additive.ofMul
          (Units.mapEquiv phi.toMulEquiv
            (chosenValuationOneUnitOfRingEquiv L M phi hmem))) = 1

end Langlands.NYLL.LocalClassFieldTheory
