/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 1199 (2026-11-01), with formulation and
   supplied-data comparison rationale by Worker 106: add a derived closed
   Type 0 comparison target for the published adaptations of M248.001,
   M248.002, M248.006 and M248.011 from upstream commit
   fbd320cd8b1b06487c58227e92eb135794267709. Retain independently supplied
   local-field structures on both fields and raw HasExtension along their
   supplied algebraMap. Compare the exact named chosen valuation with the
   canonical package of the supplied upstairs valuation, by IsEquiv and
   equality of actual valuation subrings in L. This proposition is not a
   literal upstream declaration; no proof or instance is added. The original
   LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Chosen

/-!
# Comparison of chosen and supplied local valuations: statement

The chosen valuation on a finite separable extension is equivalent to the
supplied upstairs local-field valuation, with equality of their actual
valuation subrings in that same field.
-/

namespace Langlands.NYLL.LocalFieldTheory

/-- The named chosen valuation agrees up to equivalence with the canonical
package of any supplied compatible upstairs local-field valuation, and their
actual valuation subrings in the upstairs field are equal. -/
def ChosenLocalExtensionSuppliedComparisonStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [_root_.Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)],
    (chosenLocalExtensionCompleteDVF K L).valuation.IsEquiv
        (localCompleteDVF L).valuation ∧
      (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring =
        (localCompleteDVF L).valuation.valuationSubring

end Langlands.NYLL.LocalFieldTheory
