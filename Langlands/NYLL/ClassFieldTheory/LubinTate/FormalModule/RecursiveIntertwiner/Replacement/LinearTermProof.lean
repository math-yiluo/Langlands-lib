/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 294, 2026-11-14: focused extraction of the indicated
M353 source units, namespace qualification, source-private name adaptation,
and replacement of the recursive imports by focused published dependencies.
Prepared for publication by Worker 343, 2026-11-14: retain the M353.029
proof and exact signature, and expand the source and proof documentation.
The accompanying Markdown records exact source correspondence and edits.
License and notices are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.LinearTermStatement

universe u v w

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {sigma : Type w} [Fintype sigma]

/-- Adding a monomial of total degree at least two preserves the prescribed linear term. -/
theorem d029
    {H : MvPowerSeries sigma F.valuationSubring}
    {L : sigma → F.valuationSubring}
    (hH : HasLinearTerm H L)
    (d : sigma →₀ ℕ) (hd : 2 ≤ d.degree)
    (c : F.valuationSubring) :
    d029Statement hH d hd c := by
  change HasLinearTerm (H + MvPowerSeries.monomial d c) L
  rw [HasLinearTerm]
  have hmonomial :
      (2 : ℕ∞) ≤ (MvPowerSeries.monomial d c).order := by
    apply MvPowerSeries.nat_le_order
    intro q hq
    have hqNat : q.degree < 2 := by
      exact_mod_cast hq
    have hqd : q ≠ d := by
      intro h
      have hdegree :=
        congrArg (fun x : sigma →₀ ℕ => x.degree) h
      omega
    rw [MvPowerSeries.coeff_monomial_ne hqd]
  rw [show
    H + MvPowerSeries.monomial d c - linearForm L =
      (H - linearForm L) + MvPowerSeries.monomial d c by ring]
  exact
    (le_min hH hmonomial).trans
      MvPowerSeries.min_order_le_add

end Langlands.NYLL.PortInternal.M353
