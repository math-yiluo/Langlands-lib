/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 492 on 2026-11-14: extracted the proof of the private
theorem M351.021 (`constantCoeff_monomial_eq_zero_stabilization`, lines
604–610) from
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
commit fbd320cd8b1b06487c58227e92eb135794267709, renamed it to
Langlands.NYLL.PortInternal.M351.d021 and stated it as the published
`d021Statement hd c`, which the first rewrite unfolds. The source closing
step `exact Ne.symm hd` is passed to the rewrite as the side condition.
Details are in the paired Markdown; LICENSE and NOTICE are retained in
licenses/NYLL/.

Modified by Worker 287 on 2026-11-16: retain Worker 492's proof and paired
documentation, add this provenance record, and prepare exact-target
submission against the current published statement.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.PowAddMonomial.Statements

/-!
# A nonconstant monomial has zero constant coefficient (NYLL M351.021)
-/

namespace Langlands.NYLL.PortInternal.M351

/-- M351.021: the monomial `c X^d` with `d ≠ 0` has zero constant
coefficient. -/
theorem d021
    {R : Type*} [CommRing R] {τ : Type*}
    {d : τ →₀ ℕ} (hd : d ≠ 0) (c : R) :
    d021Statement hd c := by
  rw [d021Statement, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_monomial_ne (Ne.symm hd)]

end Langlands.NYLL.PortInternal.M351
