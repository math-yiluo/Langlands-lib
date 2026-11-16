/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 560, 2026-11-16: extract only the source-private theorem
M351.016 (lines 437–479) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; publish it as
Langlands.NYLL.PortInternal.M351.d016 with the published d016Statement
as its result type; replace linearInVariableStabilization by the published
d011; qualify the opened namespaces with Langlands.NYLL; replace the source
imports by the focused published statement module; omit the unused section
Fintype instance and its omit command, noncomputable section, BigOperators
opening and local Classical.propDecidable instance; and replace the module
documentation. The coefficient proof is otherwise unchanged. The original
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Statements

/-!
# Agreement of a Lubin--Tate series with its linear model below degree two

The inserted series `ebar(X_i)` and `C π * X_i` have the same constant and
linear coefficients. Their difference therefore has order at least two.
-/

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- M351.016: `ebar(X_i)` agrees with `π·X_i` in every total degree below two. -/
theorem d016 (ebar : LubinTateSeries F π) (i : σ) :
    d016Statement ebar i := by
  show (2 : ℕ∞) ≤ (inVariable ebar i - d011 π i).order
  classical
  apply MvPowerSeries.nat_le_order
  intro d hd
  rw [map_sub]
  by_cases hdi : d = Finsupp.single i (d i)
  · by_cases hzero : d i = 0
    · have hd0 : d = 0 := by
        rw [hdi, hzero, Finsupp.single_zero]
      subst d
      simp [inVariable, d011,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.constantCoeff_eq_zero]
    · have hone : d i = 1 := by
        have hdegree : d.degree = d i := by
          simpa only [Finsupp.degree_single] using
            congrArg Finsupp.degree hdi
        have hlt : d i < 2 := by
          rw [← hdegree]
          exact hd
        omega
      have hd1 : d = Finsupp.single i 1 := by
        rw [hdi, hone]
      subst d
      simp [inVariable, d011,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.coeff_one_eq_uniformizer]
  · have hsingle : d ≠ Finsupp.single i 1 := by
      intro h
      apply hdi
      rw [h, Finsupp.single_eq_same]
    have hX :
        MvPowerSeries.coeff d
          (MvPowerSeries.X i :
            MvPowerSeries σ F.valuationSubring) = 0 := by
      rw [MvPowerSeries.coeff_X, ite_eq_right hsingle]
    simp [inVariable, d011,
      PowerSeries.coeff_subst_single, hdi, hX]

end Langlands.NYLL.PortInternal.M351
