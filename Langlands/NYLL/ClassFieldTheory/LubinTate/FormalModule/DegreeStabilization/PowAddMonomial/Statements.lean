/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 492, 14 November 2026: extract the types of the three
source-private theorems M351.021–M351.023 (source lines 604–696) of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued
targets Langlands.NYLL.PortInternal.M351.d021Statement–d023Statement.
Each target takes the source binders, in source order and binder kinds and
with source names, as parameters and has the source conclusion as its body.
Keep the source's local instance Classical.propDecidable, which supplies the
decidability of `q = d`. Omit the proofs, the unused section variables
(K, F, π, σ and [Fintype σ]) and the import of RecursiveCoefficient; import
only Mathlib.RingTheory.MvPowerSeries.Basic. The original LICENSE and NOTICE
remain in licenses/NYLL/.
-/

import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Targets for power coefficients after adding one monomial

Proposition targets for the source-private results M351.021–M351.023 of
`Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`: a
monomial of nonzero exponent has zero constant coefficient, and, for `H` with
zero constant coefficient and a monomial `c X^d` of total degree at least one,
the coefficients of `(H + c X^d) ^ n - H ^ n` and of `(H + c X^d) ^ n` in every
exponent `q` of total degree at most that of `d`. See the paired Markdown.
-/

attribute [local instance] Classical.propDecidable

namespace Langlands.NYLL.PortInternal.M351

set_option linter.unusedVariables false in
/-- Target of M351.021 (private
`LubinTate.SameUniformizer.constantCoeff_monomial_eq_zero_stabilization`):
the monomial `c X^d` with `d ≠ 0` has zero constant coefficient. -/
abbrev d021Statement
    {R : Type*} [CommRing R] {τ : Type*}
    {d : τ →₀ ℕ} (hd : d ≠ 0) (c : R) : Prop :=
  MvPowerSeries.constantCoeff (MvPowerSeries.monomial d c) = 0

set_option linter.unusedVariables false in
/-- Target of M351.022 (private
`LubinTate.SameUniformizer.coeff_pow_add_monomial_sub_pow_of_degree_le`):
if `H` has zero constant coefficient, `1 ≤ d.degree` and
`q.degree ≤ d.degree`, then the `q`-coefficient of
`(H + c X^d) ^ n - H ^ n` is `c` when `n = 1` and `q = d`, and `0` otherwise. -/
abbrev d022Statement
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q d : τ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 1 ≤ d.degree) (c : R) (n : ℕ) : Prop :=
  MvPowerSeries.coeff q
      ((H + MvPowerSeries.monomial d c) ^ n - H ^ n) =
    if n = 1 then (if q = d then c else 0) else 0

set_option linter.unusedVariables false in
/-- Target of M351.023 (private
`LubinTate.SameUniformizer.coeff_pow_add_monomial_of_degree_le`):
under the hypotheses of M351.022, the `q`-coefficient of
`(H + c X^d) ^ n` is that of `H ^ n` plus `c` when `n = 1` and `q = d`. -/
abbrev d023Statement
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (q d : τ →₀ ℕ) (hq : q.degree ≤ d.degree)
    (hd : 1 ≤ d.degree) (c : R) (n : ℕ) : Prop :=
  MvPowerSeries.coeff q
      ((H + MvPowerSeries.monomial d c) ^ n) =
    MvPowerSeries.coeff q (H ^ n) +
      if n = 1 then (if q = d then c else 0) else 0

end Langlands.NYLL.PortInternal.M351
