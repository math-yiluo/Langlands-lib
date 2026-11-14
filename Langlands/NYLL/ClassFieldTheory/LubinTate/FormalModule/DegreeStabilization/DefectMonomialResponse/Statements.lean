/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 494, 14 November 2026: extract the signatures of the
source theorems M351.024 (line 699, private), M351.025 (line 775, private)
and M351.026 (line 814) of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued
targets named `<adapted name>Statement`. The two private theorems receive
the planned names Langlands.NYLL.PortInternal.M351.d024Statement and
d025Statement; the public theorem keeps its source name in the namespace
Langlands.NYLL.LubinTate.SameUniformizer. The source section variables,
universes u v w, the `omit [Fintype σ]`/`[Finite σ]`/`[Fintype σ]`
distinctions, binder kinds and conclusions are unchanged; hypotheses that
the conclusion does not mention are underscored. The source local instance
Classical.propDecidable is kept so that `if q = d` elaborates as in the
source. The original RecursiveCoefficient and Trunc imports are replaced by
the published Intertwiner and LinearTerm definition modules. Proofs are
omitted. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions

/-!
# Targets for the response of the intertwining defect to one monomial

Exact proposition targets for three theorems of the source module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`. Adding
`c X^d` to a series `H` with zero constant coefficient changes the
coefficient of `X^q` of `e(H)` by `π * c` when `q = d` and leaves it unchanged
otherwise, provided `q.degree ≤ d.degree` and `1 ≤ d.degree`. Consequently the
intertwining defect changes, in such degrees, only in the coordinate `d`, by
`π * ((1 - π ^ (d.degree - 1)) * c)`.
-/

universe u v w

attribute [local instance] Classical.propDecidable

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- Target of M351.024 (source-private
`coeff_subst_lubinTateSeries_add_monomial_of_degree_le`): if `H` has zero
constant coefficient, `q.degree ≤ d.degree` and `1 ≤ d.degree`, then adding
the monomial `c X^d` to `H` changes the coefficient of `X^q` in `e(H)` by
`π * (if q = d then c else 0)`. No finite-variable hypothesis is assumed. -/
abbrev d024Statement
    (e : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    (_hH : MvPowerSeries.constantCoeff H = 0)
    (q d : σ →₀ ℕ) (_hq : q.degree ≤ d.degree)
    (_hd : 1 ≤ d.degree) (c : F.valuationSubring) : Prop :=
  MvPowerSeries.coeff q
      (PowerSeries.subst
        (H + MvPowerSeries.monomial d c)
        e.toPowerSeries) =
    MvPowerSeries.coeff q
        (PowerSeries.subst H e.toPowerSeries) +
      π * (if q = d then c else 0)

/-- Target of M351.025 (source-private
`coeff_defect_add_monomial_eq_of_degree_le_constantCoeff`): over a finite
variable type, if `H` has zero constant coefficient, `q.degree ≤ d.degree`
and `1 ≤ d.degree`, then adding `c X^d` to `H` changes the coefficient of
`X^q` in the defect of `H` by `π * ((1 - π ^ (d.degree - 1)) * c)` when
`q = d` and by zero otherwise. -/
abbrev d025Statement [Finite σ]
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    (_hH : MvPowerSeries.constantCoeff H = 0)
    (q d : σ →₀ ℕ) (_hq : q.degree ≤ d.degree)
    (_hd : 1 ≤ d.degree) (c : F.valuationSubring) : Prop :=
  MvPowerSeries.coeff q
      (defect e ebar (H + MvPowerSeries.monomial d c)) =
    MvPowerSeries.coeff q (defect e ebar H) +
      if q = d then
        π * ((1 - π ^ (d.degree - 1)) * c)
      else 0

end Langlands.NYLL.PortInternal.M351

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- Target of M351.026 (`coeff_defect_add_monomial_eq_of_degree_le`): for a
series `H` with prescribed linear term `L`, `q.degree ≤ d.degree` and
`2 ≤ d.degree`, adding the monomial `c X^d` changes no defect coefficient in
total degree below `d.degree`, and in total degree `d.degree` changes only
the coefficient of `X^d`, by `π * ((1 - π ^ (d.degree - 1)) * c)`. -/
abbrev coeff_defect_add_monomial_eq_of_degree_leStatement [Fintype σ]
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (_hH : HasLinearTerm H L)
    (q d : σ →₀ ℕ) (_hq : q.degree ≤ d.degree)
    (_hd : 2 ≤ d.degree) (c : F.valuationSubring) : Prop :=
  MvPowerSeries.coeff q
      (defect e ebar (H + MvPowerSeries.monomial d c)) =
    MvPowerSeries.coeff q (defect e ebar H) +
      if q = d then
        π * ((1 - π ^ (d.degree - 1)) * c)
      else 0

end SameUniformizer
end Langlands.NYLL.LubinTate
