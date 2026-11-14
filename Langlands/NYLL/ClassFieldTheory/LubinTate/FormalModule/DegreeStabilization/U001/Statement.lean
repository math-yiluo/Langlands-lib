/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 488, 2026-11-14: extract the statement of the source
theorem M351.001 (`truncTotal_succ_eq_iff_coeff_eq_degree_le`, source lines
40–48 of Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as the
Prop-valued target `truncTotal_succ_eq_iff_coeff_eq_degree_leStatement`;
prefix the namespace with Langlands.NYLL; replace the source imports by the
single Mathlib module Mathlib.RingTheory.MvPowerSeries.Trunc; omit the source
`noncomputable section`, `open scoped BigOperators`, `universe u v w`,
`open LocalFieldTheory.DiscreteValuationField` and the later section
variables, none of which the source theorem uses; omit the source proof.
The binders and the conclusion are those of the source theorem. The original
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Total-degree truncation through degree `m`

Proposition target for the source theorem M351.001: two multivariable power
series over a finite variable type have the same total-degree truncation
`truncTotal (m + 1)` exactly when their coefficients agree in every total
degree at most `m`.
-/

attribute [local instance] Classical.propDecidable

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

/-- Target of M351.001 (`truncTotal_succ_eq_iff_coeff_eq_degree_le`):
equality of total-degree truncations through degree `m` is equivalent to
coefficientwise equality in every total degree at most `m`. -/
abbrev truncTotal_succ_eq_iff_coeff_eq_degree_leStatement
    {R : Type*} [CommSemiring R]
    {τ : Type*} [Finite τ]
    {H H' : MvPowerSeries τ R} (m : ℕ) : Prop :=
  H.truncTotal (m + 1) = H'.truncTotal (m + 1) ↔
    ∀ d : τ →₀ ℕ, d.degree ≤ m →
      MvPowerSeries.coeff d H = MvPowerSeries.coeff d H'

end SameUniformizer
end Langlands.NYLL.LubinTate
