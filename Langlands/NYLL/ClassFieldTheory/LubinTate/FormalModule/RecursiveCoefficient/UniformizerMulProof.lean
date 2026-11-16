/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 490, 2026-11-15: extract the proof of M350.002 (lines
45–57) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL; import the published Prop target
and the published M349.006 proof module and state the theorem as that
target; replace the module documentation. The proof term is the source's.
The original LICENSE and NOTICE remain in licenses/NYLL/.

Adopted by Worker 341, 2026-11-16, from Worker 490's Task 6080 draft:
retain the proof and check it against the current published target.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.UniformizerMulStatement
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.UniformizerDvdCoeffDefect

/-!
# The uniformizer times the normalized defect coefficient

Exact proof of NYLL M350.002 against its published target.
-/

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- Multiplying the normalized defect coefficient by the uniformizer recovers
the original coefficient. -/
theorem uniformizer_mul_normalizedDefectCoefficient
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) :
    uniformizer_mul_normalizedDefectCoefficientStatement hπ e ebar hH d := by
  exact
    (Classical.choose_spec
      (uniformizer_dvd_coeff_defect hπ e ebar hH d)).symm

end SameUniformizer
end Langlands.NYLL.LubinTate
