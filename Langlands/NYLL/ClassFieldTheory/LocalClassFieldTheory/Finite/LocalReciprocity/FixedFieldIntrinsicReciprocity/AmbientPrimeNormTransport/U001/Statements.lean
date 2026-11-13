/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the asserted type of M283.001 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and package all eleven original binders inside a closed Prop-valued
definition, preserving their order, the source's universe-zero field types and
the conjunction in the conclusion. The named hypothesis hmem becomes an
anonymous premise of the same type.
Write the published normalized valuation map by its full name instead of
using the source namespace openings, and replace the source imports by the
single published module that defines it. Defer the truth proof; install no
instance or simp registration. Omit the original noncomputable section, the
namespace openings and all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions

/-!
# Valuation-one units under valuation-compatible ring equivalences

The closed assertion that a ring equivalence between two nonarchimedean
local fields which matches their valuation subrings carries some unit of
normalized valuation one to a unit of normalized valuation one.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- A valuation-subring-preserving ring equivalence carries some unit of
valuation one to a unit of valuation one. -/
def exists_valuationOne_unit_of_ringEquivStatement : Prop :=
  ∀ (L M : Type)
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M]
    (phi : L ≃+* M),
    (∀ x : L,
      x ∈ (ValuativeRel.valuation L).valuationSubring ↔
        phi x ∈ (ValuativeRel.valuation M).valuationSubring) →
    ∃ p : Lˣ,
      Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap L
          (Additive.ofMul p) = 1 ∧
        Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap M
          (Additive.ofMul
            (Units.mapEquiv phi.toMulEquiv p)) = 1

end Langlands.NYLL.LocalClassFieldTheory
