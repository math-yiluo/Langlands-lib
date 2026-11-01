/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 785 (2026-10-31): extract only M248.006 from
   upstream commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the
   namespace with Langlands.NYLL, and replace the private M248.005 wrapper
   chosenLocalExtensionCompleteDVF_exists by a direct specialization of the
   published existence theorem
   exists_integralClosure_standard_completeDVF_extension at universes 0, 0, 0
   and the published canonical base localCompleteDVF K. Replace the original
   imports by the two published modules supplying these declarations. The
   original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.StandardCompleteDVFExtensionProof

/-!
# A chosen complete discrete valuation on a finite local extension

On an arbitrary finite separable extension of a nonarchimedean local field,
a complete discrete valuation chosen from the published existence of a
complete-DVF extension of the canonical base valuation whose valuation
subring is the actual integral closure.
-/

noncomputable section

namespace Langlands.NYLL.LocalFieldTheory

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- A complete discrete valuation on an arbitrary finite separable extension
of a nonarchimedean local field, chosen from its actual integral closure. -/
noncomputable def chosenLocalExtensionCompleteDVF
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    CompleteDVF.{0, 0} L :=
  Classical.choose
    (exists_integralClosure_standard_completeDVF_extension.{0, 0, 0}
      K L (localCompleteDVF K))

end Langlands.NYLL.LocalFieldTheory
