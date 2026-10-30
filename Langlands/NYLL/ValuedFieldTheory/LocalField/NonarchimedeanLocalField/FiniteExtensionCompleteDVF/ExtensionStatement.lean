/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 785 (2026-10-30): extract only the statement of
   M248.002, `LocalFieldTheory.localCompleteDVFValuation_hasExtension`, from
   upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as a closed
   Prop-valued definition without its proof, rename it to
   `LocalCompleteDVFValuationHasExtensionStatement`, prefix the namespace with
   Langlands.NYLL, write the conclusion `Valuation.HasExtension` in prefix form,
   and replace the original imports by Mathlib.RingTheory.Valuation.Extension
   and the published M248.001 module. The original LICENSE and NOTICE are
   retained in licenses/NYLL/. -/

import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical

/-!
# Extension compatibility of the canonical complete-DVF packages

The statement that the canonical complete discrete valuations of two
nonarchimedean local fields preserve an existing extension of their canonical
valuations.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- The canonical complete-DVF packages preserve an existing extension of
the underlying valuative relations. -/
def LocalCompleteDVFValuationHasExtensionStatement : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [_root_.Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)],
    _root_.Valuation.HasExtension (localCompleteDVF K).valuation
      (localCompleteDVF L).valuation

end Langlands.NYLL.LocalFieldTheory
