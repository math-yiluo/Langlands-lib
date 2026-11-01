/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 785 (2026-10-31): extract only the proofs of
   M248.007 `chosenLocalExtensionCompleteDVF_hasExtension`, M248.009
   `chosenLocalExtensionCompleteDVF_isIntegralClosure` and M248.010
   `chosenLocalExtensionCompleteDVF_valuationSubring_moduleFinite` from
   upstream commit fbd320cd8b1b06487c58227e92eb135794267709, and combine them
   into one theorem whose type is the published closed proposition
   `ChosenLocalExtensionPropertiesStatement`. The two `Classical.choose_spec`
   steps are applied to the published existence theorem
   `exists_integralClosure_standard_completeDVF_extension` at universes
   0, 0, 0, which defines the published M248.006 choice, instead of the
   private M248.005 wrapper. The M248.007 witness is a local `let`, not the
   global M248.008 instance, which is omitted. Prefix the namespace with
   Langlands.NYLL, and replace the original imports by the published
   statement module and Mathlib's Dedekind-domain integral-closure module.
   The original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenPropertiesStatement

/-!
# Properties of the chosen complete discrete valuation on a finite local extension: proof

The chosen complete discrete valuation on a finite separable extension of a
nonarchimedean local field extends the canonical valuation of the base. With
that extension witness, its valuation subring is the actual integral closure
of the canonical base valuation subring and a finite module over it.
-/

namespace Langlands.NYLL.LocalFieldTheory

open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The chosen valuation on a finite separable extension of a nonarchimedean
local field extends the canonical valuation of the base field. With that
extension witness, the chosen valuation ring is the actual integral closure of
the canonical base valuation ring and a finite module over it. -/
theorem chosenLocalExtension_properties :
    ChosenLocalExtensionPropertiesStatement := by
  intro K L _ _ _ _ _ _ _ _
  have hChosen := Classical.choose_spec
    (exists_integralClosure_standard_completeDVF_extension.{0, 0, 0}
      K L (localCompleteDVF K))
  let hExt : _root_.Valuation.HasExtension
      (localCompleteDVF K).valuation
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose hChosen
  have hIntegralClosure : IsIntegralClosure
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring
      (localCompleteDVF K).valuation.valuationSubring L :=
    Classical.choose_spec hChosen
  exact ⟨hExt, hIntegralClosure,
    IsIntegralClosure.finite
      (localCompleteDVF K).valuation.valuationSubring K L
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring⟩

end Langlands.NYLL.LocalFieldTheory
