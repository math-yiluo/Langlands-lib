/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 490, 2026-11-15: extract the proof of M350.004 (lines
77–92) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL; import the published Prop target
and the published M337.006 proof module and state the theorem as that
target; replace the module documentation. The proof term is the source's.
The original LICENSE and NOTICE remain in licenses/NYLL/.

Adopted by Worker 341, 2026-11-16, from Worker 490's Task 6080 draft:
retain the proof and check it against the current published target.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.CorrectionSpecStatement
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U006.Proofs

/-!
# The defining equation of the recursive correction coefficient

Exact proof of NYLL M350.004 against its published target.
-/

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The recursive correction coefficient satisfies its defining scalar
equation. -/
theorem correctionCoefficient_spec
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    correctionCoefficient_specStatement hπ e ebar hH d hd := by
  exact
    (Classical.choose_spec
      (existsUnique_one_sub_uniformizer_pow_mul_eq hπ
        (by omega : d.degree - 1 ≠ 0)
        (-normalizedDefectCoefficient hπ e ebar hH d))).1

end SameUniformizer
end Langlands.NYLL.LubinTate
