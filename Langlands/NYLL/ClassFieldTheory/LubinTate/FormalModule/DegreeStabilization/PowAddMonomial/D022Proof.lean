/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 492 on 2026-11-14: proved the private theorem M351.022
(`coeff_pow_add_monomial_sub_pow_of_degree_le`, lines 612–680) of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
commit fbd320cd8b1b06487c58227e92eb135794267709 as
Langlands.NYLL.PortInternal.M351.d022, stated as the published
`d022Statement hH q d hq hd c n`. The case split n = 0, n = 1, n ≥ 2 and the
proof of d ≠ 0 follow the source. For n ≥ 2 the source's order estimate
(M351.005, M351.009 and M351.021) is replaced by a direct coefficient
computation: the difference of powers factors as a geometric sum times the
monomial, whose q-coefficient is zero for degree reasons. Details are in the
paired Markdown; LICENSE and NOTICE are retained in licenses/NYLL/.

Modified by Worker 185 on 2026-11-16: adopt Worker 492's shared draft
for the focused exact-proof task, retaining the proof and documenting the
shared draft provenance in the paired Markdown.
-/

import Mathlib.Algebra.Ring.GeomSum
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.PowAddMonomial.Statements

/-!
# Low-degree coefficients of `(H + c X^d) ^ n - H ^ n` (NYLL M351.022)
-/

namespace Langlands.NYLL.PortInternal.M351

/-- M351.022: if `H` has zero constant coefficient, `1 ≤ d.degree` and
`q.degree ≤ d.degree`, then the `q`-coefficient of `(H + c X^d) ^ n - H ^ n`
is `c` when `n = 1` and `q = d`, and `0` otherwise. -/
theorem d022
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q d : τ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 1 ≤ d.degree) (c : R) (n : ℕ) :
    d022Statement hH q d hq hd c n := by
  unfold d022Statement
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hd
  rcases n with _ | _ | n
  · simp
  · classical
    simp only [zero_add, pow_one, add_sub_cancel_left, ↓reduceIte]
    convert MvPowerSeries.coeff_monomial q d c
  · have hM : MvPowerSeries.constantCoeff (MvPowerSeries.monomial d c) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        MvPowerSeries.coeff_monomial_ne (Ne.symm hd0)]
    rw [← geom_sum₂_mul, add_sub_cancel_left, MvPowerSeries.coeff_mul_monomial]
    have hS : MvPowerSeries.constantCoeff
        (∑ i ∈ Finset.range (n + 2), (H + MvPowerSeries.monomial d c) ^ i *
          H ^ (n + 2 - 1 - i)) = 0 := by
      simp only [map_sum, map_mul, map_pow, map_add, hH, hM, add_zero]
      refine Finset.sum_eq_zero fun i hi => ?_
      rcases i with _ | i
      · simp
      · simp
    simp only [show n + 1 + 1 ≠ 1 by omega, ↓reduceIte]
    split_ifs with hdq
    · have hqd : q - d = 0 := by
        rw [← Finsupp.degree_eq_zero_iff]
        have h2 : (q - d).degree + d.degree = q.degree := by
          rw [← map_add, tsub_add_cancel_of_le hdq]
        omega
      rw [hqd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hS, zero_mul]
    · rfl

end Langlands.NYLL.PortInternal.M351
