/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 343 on 2026-11-16: extract M352.003 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix its namespace with
Langlands.NYLL, import the published RecursiveCorrection.Statements module,
and express its conclusion through the published Statement target. Unfold
that target in the proof's initial rewrite; the remaining proof is unchanged.
Omit the unused noncomputable section and open scoped BigOperators, and
replace the module documentation. LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection.Statements

/-!
# Preservation of the linear term by a recursive correction

A monomial correction of total degree at least two preserves the prescribed
linear term of the current same-uniformizer intertwiner approximation.
-/

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- A correction in total degree at least two does not change the prescribed
linear term. -/
theorem correctedIntertwiner_hasLinearTerm
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    correctedIntertwiner_hasLinearTermStatement hπ e ebar hH d hd := by
  classical
  rw [correctedIntertwiner_hasLinearTermStatement, correctedIntertwiner, HasLinearTerm]
  have hd' : (2 : ℕ∞) ≤ (d.degree : ℕ∞) := by
    exact_mod_cast hd
  have hcorrection :
      (2 : ℕ∞) ≤ (monomialCorrection hπ e ebar hH d hd).order := by
    rw [monomialCorrection, MvPowerSeries.order_monomial]
    split_ifs
    · exact le_top
    · exact hd'
  rw [show
    H + monomialCorrection hπ e ebar hH d hd - linearForm L =
      (H - linearForm L) +
        monomialCorrection hπ e ebar hH d hd by ring]
  exact
    (le_min hH hcorrection).trans
      MvPowerSeries.min_order_le_add

end SameUniformizer
end Langlands.NYLL.LubinTate
