/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 785 (2026-10-31): extract only the statements of
   M248.007 `chosenLocalExtensionCompleteDVF_hasExtension`, M248.009
   `chosenLocalExtensionCompleteDVF_isIntegralClosure` and M248.010
   `chosenLocalExtensionCompleteDVF_valuationSubring_moduleFinite` from
   upstream commit fbd320cd8b1b06487c58227e92eb135794267709, without their
   proofs, and group them as one closed Prop-valued definition
   `ChosenLocalExtensionPropertiesStatement` quantifying their shared
   telescope. The global M248.008 instance
   `chosenLocalExtensionCompleteDVF.instHasExtension` is omitted: the
   HasExtension conclusion becomes an existential witness, installed with
   letI for the two other conclusions. Expand the CompleteDVF valuationSubring
   abbreviations, write Valuation.HasExtension in prefix form, prefix the
   namespace with Langlands.NYLL, and replace the original imports by the
   published M248.006 module and focused Mathlib imports. The original
   LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Chosen

/-!
# Properties of the chosen complete discrete valuation on a finite local extension

The statement that the chosen complete discrete valuation on a finite
separable extension of a nonarchimedean local field extends the canonical
valuation of the base, and that, with this extension witness, its valuation
subring is the actual integral closure of the canonical base valuation subring
and a finite module over it.
-/

namespace Langlands.NYLL.LocalFieldTheory

/-- The chosen valuation on a finite separable extension of a nonarchimedean
local field extends the canonical valuation of the base field. With that
extension witness, the chosen valuation ring is the actual integral closure of
the canonical base valuation ring and a finite module over it. -/
def ChosenLocalExtensionPropertiesStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    ∃ hExt : _root_.Valuation.HasExtension
        (localCompleteDVF K).valuation
        (chosenLocalExtensionCompleteDVF K L).valuation,
      letI : _root_.Valuation.HasExtension
          (localCompleteDVF K).valuation
          (chosenLocalExtensionCompleteDVF K L).valuation := hExt
      IsIntegralClosure
          (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring
          (localCompleteDVF K).valuation.valuationSubring L ∧
        Module.Finite
          (localCompleteDVF K).valuation.valuationSubring
          (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring

end Langlands.NYLL.LocalFieldTheory
