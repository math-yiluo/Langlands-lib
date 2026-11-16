/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 519, 2026-11-16: prove the published exact M351.028
signature from pinned NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
DegreeStabilization.lean lines 841–888, by a direct low-degree substitution
argument with private helpers. Prefix the namespace, use the focused published
imports, and retain the original LICENSE and NOTICE in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LowDegreeDefect.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.InVariableHasSubst
import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# Low-degree vanishing of the defect of a finite linear sum

The two substitutions have the same coefficients in total degree at most one.
-/

universe u v w

namespace Langlands.NYLL

open LubinTate LubinTate.SameUniformizer
open LocalFieldTheory.DiscreteValuationField

namespace PortInternal.M351

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

private theorem coeff_subst_low_for_linear_sum
    (e : LubinTateSeries F π) {H : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q : σ →₀ ℕ) (hq : q.degree ≤ 1) :
    MvPowerSeries.coeff q (PowerSeries.subst H e.toPowerSeries) =
      π * MvPowerSeries.coeff q H := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hH),
    finsum_eq_single _ 1]
  · simp only [pow_one, LubinTateSeries.coeff_one_eq_uniformizer, smul_eq_mul]
  · intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, e.constantCoeff_eq_zero]
    · have hqn : q.degree < n := by omega
      have hz : MvPowerSeries.coeff q (H ^ n) = 0 :=
        MvPowerSeries.coeff_of_lt_order
          (lt_of_lt_of_le (by exact_mod_cast hqn)
            (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n hH))
      rw [hz, smul_zero]

/-- The defect of any finite sum of linear monomials has zero coefficients
in total degree at most one (NYLL M351.028). -/
theorem d028 [Finite σ]
    (e ebar : LubinTateSeries F π)
    (L : σ → F.valuationSubring)
    (s : Finset σ) (q : σ →₀ ℕ) (hq : q.degree ≤ 1) :
    d028Statement e ebar L s q hq := by
  classical
  have hmono (i : σ) :
      MvPowerSeries.monomial (Finsupp.single i 1) (L i) =
        L i • (MvPowerSeries.X i : MvPowerSeries σ F.valuationSubring) := by
    rw [MvPowerSeries.X_def, ← map_smul, smul_eq_mul, mul_one]
  have hconstant : MvPowerSeries.constantCoeff
      (∑ i ∈ s, MvPowerSeries.monomial (Finsupp.single i 1) (L i)) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_monomial_ne]
    exact (Finsupp.single_ne_zero.mpr one_ne_zero).symm
  change MvPowerSeries.coeff q (PowerSeries.subst _ e.toPowerSeries -
    MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) _) = 0
  rw [map_sub, coeff_subst_low_for_linear_sum e hconstant q hq, sub_eq_zero]
  rw [← MvPowerSeries.substAlgHom_apply (inVariable_hasSubst ebar), map_sum,
    map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hmono, map_smul, MvPowerSeries.substAlgHom_X, smul_eq_mul]
  rw [inVariable, coeff_subst_low_for_linear_sum ebar
    (MvPowerSeries.constantCoeff_X i) q hq]
  ring

end PortInternal.M351
end Langlands.NYLL
