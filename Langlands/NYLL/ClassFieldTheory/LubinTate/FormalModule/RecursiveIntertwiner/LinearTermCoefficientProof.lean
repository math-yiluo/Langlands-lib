/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 344, 14 November 2026: extract only the proof of private
source unit M353.043 from commit fbd320cd8b1b06487c58227e92eb135794267709,
rename it Langlands.NYLL.PortInternal.M353.d043, and make its complete
effective source telescope explicit in the theorem declaration. Replace
the broad recursive imports by the published exact target module, add a
complete-type check against that target, and focus the documentation.
The source proof, universe independence, binder kinds, hypotheses and
conclusion are unchanged. See the paired Markdown and licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.LinearTermCoefficientStatement

/-!
# Low-degree coefficients of a series with a prescribed linear term

This module proves the published M353.043 target as
`Langlands.NYLL.PortInternal.M353.d043`.
-/

noncomputable section

universe u v w

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate.SameUniformizer

/-- A series with prescribed linear term agrees with that linear form
at every exponent of total degree below two. -/
theorem d043
    {K : Type u} [Field K] {F : LocalField.{u, v} K}
    {sigma : Type w} [Fintype sigma]
    {H : MvPowerSeries sigma F.valuationSubring}
    {L : sigma → F.valuationSubring}
    (hH : HasLinearTerm H L)
    (d : sigma →₀ ℕ) (hd : d.degree < 2) :
    MvPowerSeries.coeff d H =
      MvPowerSeries.coeff d (linearForm L) := by
  have hd' : (d.degree : ℕ∞) < (2 : ℕ∞) := by
    exact_mod_cast hd
  have hzero :=
    MvPowerSeries.coeff_of_lt_order (hd'.trans_le hH)
  rw [map_sub, sub_eq_zero] at hzero
  exact hzero

/-- Check the entire unapplied theorem against the exact published target. -/
example : d043Statement.{u, v, w} := @d043.{u, v, w}

end Langlands.NYLL.PortInternal.M353

end
