/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 488, 2026-11-14: the proof of the source theorem M351.001
(`truncTotal_succ_eq_iff_coeff_eq_degree_le`, source lines 42–66 of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean,
upstream commit fbd320cd8b1b06487c58227e92eb135794267709), stated against the
published target `truncTotal_succ_eq_iff_coeff_eq_degree_leStatement`; the
namespace is prefixed with Langlands.NYLL and the import is the published
statement module. The proof script is the source's, unchanged. The original
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.U001.Statement

/-!
# Total-degree truncation through degree `m`: proof

Proof of M351.001: two multivariable power series have the same total-degree
truncation `truncTotal (m + 1)` exactly when their coefficients agree in
every total degree at most `m`.
-/

attribute [local instance] Classical.propDecidable

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

/-- M351.001: equality of total-degree truncations through degree `m` is
equivalent to coefficientwise equality in every total degree at most `m`. -/
theorem truncTotal_succ_eq_iff_coeff_eq_degree_le
    {R : Type*} [CommSemiring R]
    {τ : Type*} [Finite τ]
    {H H' : MvPowerSeries τ R} (m : ℕ) :
    truncTotal_succ_eq_iff_coeff_eq_degree_leStatement (H := H) (H' := H') m := by
  constructor
  · intro h d hd
    have hd' : d.degree < m + 1 := Nat.lt_succ_iff.mpr hd
    calc
      MvPowerSeries.coeff d H =
          (H.truncTotal (m + 1)).coeff d :=
        (MvPowerSeries.coeff_truncTotal H hd').symm
      _ = (H'.truncTotal (m + 1)).coeff d := by rw [h]
      _ = MvPowerSeries.coeff d H' :=
        MvPowerSeries.coeff_truncTotal H' hd'
  · intro h
    ext d
    by_cases hd : d.degree < m + 1
    · rw [MvPowerSeries.coeff_truncTotal H hd,
        MvPowerSeries.coeff_truncTotal H' hd]
      exact h d (Nat.lt_succ_iff.mp hd)
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero H (not_lt.mp hd),
        MvPowerSeries.coeff_truncTotal_eq_zero H' (not_lt.mp hd)]

end SameUniformizer
end Langlands.NYLL.LubinTate
