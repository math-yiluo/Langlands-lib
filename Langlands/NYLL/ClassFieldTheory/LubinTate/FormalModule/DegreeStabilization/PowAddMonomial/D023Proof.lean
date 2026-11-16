/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 492 on 2026-11-14: extracted the proof of the private
theorem M351.023 (`coeff_pow_add_monomial_of_degree_le`, lines 682–696) from
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
commit fbd320cd8b1b06487c58227e92eb135794267709, renamed it to
Langlands.NYLL.PortInternal.M351.d023 and stated it as the published
`d023Statement hH q d hq hd c n`, opened by `unfold`. The source's use of
M351.022 now cites Langlands.NYLL.PortInternal.M351.d022, whose statement is
unfolded at the hypothesis, and the final `simpa [add_comm]` is replaced by
`rw [h, add_comm]`. Details are in the paired Markdown; LICENSE and NOTICE
are retained in licenses/NYLL/.

Modified by Worker 573 on 2026-11-16: prepare the supplied proof draft for
Task 6726, checking the unchanged target binders and source correspondence.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.PowAddMonomial.D022Proof

/-!
# Low-degree coefficients of `(H + c X^d) ^ n` (NYLL M351.023)
-/

namespace Langlands.NYLL.PortInternal.M351

/-- M351.023: under the hypotheses of M351.022, the `q`-coefficient of
`(H + c X^d) ^ n` is that of `H ^ n` plus `c` when `n = 1` and `q = d`. -/
theorem d023
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q d : τ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 1 ≤ d.degree) (c : R) (n : ℕ) :
    d023Statement hH q d hq hd c n := by
  have h := d022 hH q d hq hd c n
  unfold d022Statement at h
  unfold d023Statement
  rw [map_sub, sub_eq_iff_eq_add] at h
  rw [h, add_comm]

end Langlands.NYLL.PortInternal.M351
