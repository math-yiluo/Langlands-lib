/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 490, 2026-11-14: extract only the definition M350.003
(lines 59–75) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, replace the source Reduction import
by the published M350.001 definition module and the published module of the
exact M337.006 proof, omit the other source declarations (published
separately) and replace the module documentation. The declaration
docstring, binders, type and body are unchanged. The original LICENSE and
NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.NormalizedDefect
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U006.Proofs

/-!
# Recursive correction coefficients

In total degree `m ≥ 2` the scalar equation `(1 - π ^ (m - 1)) * c = b` has a
unique solution `c` in the valuation subring. This module chooses the
solution for `b` the negative of the normalized defect coefficient.
-/

noncomputable section

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The coefficient added in total degree `d.degree` by the recursive
same-uniformizer intertwiner construction.

Its defining equation is the one which cancels the normalized defect in that
degree.  The hypothesis `2 ≤ d.degree` ensures that the exponent
`d.degree - 1` is positive. -/
noncomputable def correctionCoefficient
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    F.valuationSubring :=
  Classical.choose
    (existsUnique_one_sub_uniformizer_pow_mul_eq hπ
      (by omega : d.degree - 1 ≠ 0)
      (-normalizedDefectCoefficient hπ e ebar hH d))

end SameUniformizer
end Langlands.NYLL.LubinTate

end
