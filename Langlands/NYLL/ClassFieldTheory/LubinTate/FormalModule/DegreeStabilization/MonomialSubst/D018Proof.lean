/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 259, 2026-11-16: extract the proof of the source-private
theorem M351.018 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; publish it as
`Langlands.NYLL.PortInternal.M351.d018` with the exact published
`d018Statement` as its type; replace `linearInVariableStabilization` by
the published `d011`; qualify the opened LocalField namespace with
Langlands.NYLL; and replace the original imports with the published target
module. Unfold the target before the otherwise unchanged source proof.
Omit the unused BigOperators scope and the section Fintype instance that
the source theorem explicitly omits. The original LICENSE and NOTICE
remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.MonomialSubst.LinearStatements

/-!
# Coefficients of a monomial under linear substitution

The exact proof of M351.018: substitution of `X_i ↦ π X_i` in `c X^d`
has coefficient `π ^ d.degree * c` at `d`, and zero elsewhere.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- M351.018: the coefficient formula for substituting `X_i ↦ π X_i`
into a monomial, with no finiteness hypothesis on the variable type. -/
theorem d018 (q d : σ →₀ ℕ) (c : F.valuationSubring) :
    d018Statement (π := π) q d c := by
  unfold d018Statement
  have hlinear :
      (Function.const σ π •
          (MvPowerSeries.X :
            σ → MvPowerSeries σ F.valuationSubring)) =
        d011 (σ := σ) π := by
    funext i
    simp [d011, Pi.smul_apply',
      MvPowerSeries.smul_eq_C_mul]
  rw [← hlinear, ← MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.coeff_rescale]
  by_cases hqd : q = d
  · subst q
    rw [MvPowerSeries.coeff_monomial_same, ite_eq_left rfl]
    simp only [Finsupp.prod, Function.const_apply,
      Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  · rw [MvPowerSeries.coeff_monomial_ne hqd, mul_zero,
      ite_eq_right hqd]

end Langlands.NYLL.PortInternal.M351

end
