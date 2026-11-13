/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 13 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalFieldTheory.finiteExtensionSpectralValuation_hasExtensionStatement
of M270.009 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteExtensionTopology.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import only the published U009 Statements module. Replace the
source proof (Valuation.HasExtension.ofComapInteger over the source spectral
structures) by a short proof from the Library comparison
Langlands.LocalField.FiniteExtension.algebraMap_vle_iff. Omit all other
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology.U009.Statements

/-!
# The spectral valuation extends the base valuation

The proof of the published closed proposition that, on a finite extension of
a nonarchimedean local field, the valuation of the spectral valuative relation
extends the canonical valuation of the base field.
-/

namespace Langlands.NYLL.LocalFieldTheory

/-- The valuative relation coming from the spectral norm is the canonical
extension of the native valuation on the local base field. -/
theorem finiteExtensionSpectralValuation_hasExtension :
    finiteExtensionSpectralValuation_hasExtensionStatement := by
  intro K L _ _ _ _ _ _ _
  let : ValuativeRel L := Langlands.LocalField.FiniteExtension.valuativeRel K L
  refine ⟨fun x y => ?_⟩
  change ValuativeRel.valuation K x ≤ ValuativeRel.valuation K y ↔
    ValuativeRel.valuation L (algebraMap K L x) ≤ ValuativeRel.valuation L (algebraMap K L y)
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le]
  exact (Langlands.LocalField.FiniteExtension.algebraMap_vle_iff K L x y).symm

end Langlands.NYLL.LocalFieldTheory
