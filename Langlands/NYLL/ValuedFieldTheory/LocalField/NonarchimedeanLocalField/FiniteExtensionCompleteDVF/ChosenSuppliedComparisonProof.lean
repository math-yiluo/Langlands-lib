/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 1199 (2026-11-01), with composition-route
   guidance by Worker 106: prove the derived closed
   Type 0 chosen/supplied comparison target using the published adaptations
   of M248.002 and M248.011 from upstream commit
   fbd320cd8b1b06487c58227e92eb135794267709. Install canonical extension
   compatibility locally, specialize chosen uniqueness to the supplied
   upstairs canonical valuation, and derive actual valuation-subring
   equality with Mathlib's equivalence criterion. Preserve the named chosen
   construction, all supplied structures and their algebraMap. This combined
   result is not a literal upstream declaration. The original LICENSE and
   NOTICE are retained in licenses/NYLL/. -/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenSuppliedComparisonStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ExtensionProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenUniquenessProof

/-!
# Comparison of chosen and supplied local valuations: proof

Canonical extension compatibility lets chosen-valuation uniqueness compare
the named chosen valuation with the supplied upstairs valuation. Equivalent
valuations have equal actual valuation subrings.
-/

namespace Langlands.NYLL.LocalFieldTheory

/-- The chosen valuation is equivalent to the supplied compatible upstairs
valuation, and their actual valuation subrings in the upstairs field agree. -/
theorem chosenLocalExtension_suppliedComparison :
    ChosenLocalExtensionSuppliedComparisonStatement := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _
  let : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
      (localCompleteDVF L).valuation :=
    localCompleteDVFValuation_hasExtension K L
  have hEquiv := chosenLocalExtension_uniqueValuationExtension K L
    (localCompleteDVF L).valuation
  exact ⟨hEquiv, (_root_.Valuation.isEquiv_iff_valuationSubring _ _).mp hEquiv⟩

end Langlands.NYLL.LocalFieldTheory
