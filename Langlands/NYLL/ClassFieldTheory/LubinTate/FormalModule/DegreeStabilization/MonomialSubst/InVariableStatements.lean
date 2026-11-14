/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 493, 2026-11-14: extract the propositions of the source
private theorems M351.019 and M351.020 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued targets
`Langlands.NYLL.PortInternal.M351.d019Statement` and `d020Statement`; open
the Langlands.NYLL namespaces of the published LocalField, LubinTateSeries
and inVariable, import only the published Intertwiner definition module, and
omit the proofs. The section variables, the source `omit [Fintype σ]` with
its `[Finite σ]` premise, all explicit parameters and the local classical
decidability instance are retained. The targets are reducible (`abbrev`) so
that their later proofs rewrite like the source theorems. The original
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions

/-!
# Low-degree coefficients of a monomial substituted into Lubin--Tate variables

Proposition targets for two source-private theorems of
`Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`.
Substituting `X_i ↦ ebar(X_i)` into the monomial `c X^d` gives a series whose
coefficients in total degree at most `|d|` are those of `π^|d| c X^d`; adding
the monomial to an arbitrary series adds this diagonal response to the old
substituted coefficient.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- Target of M351.019 (source `coeff_subst_inVariables_monomial_of_degree_le`):
for a finite variable type, the coefficient in a total degree `q.degree ≤
d.degree` of the monomial `c X^d` with `X_i ↦ ebar(X_i)` substituted is
`π ^ d.degree * c` when `q = d` and zero otherwise. -/
abbrev d019Statement [Finite σ]
    (ebar : LubinTateSeries F π)
    (q d : σ →₀ ℕ) (_hq : q.degree ≤ d.degree)
    (c : F.valuationSubring) : Prop :=
  MvPowerSeries.coeff q
      (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
        (MvPowerSeries.monomial d c)) =
    if q = d then π ^ d.degree * c else 0

/-- Target of M351.020 (source
`coeff_subst_inVariables_add_monomial_of_degree_le`): for a finite variable
type and an arbitrary series `H`, adding `c X^d` changes the substituted
coefficient in a total degree `q.degree ≤ d.degree` by `π ^ d.degree * c` when
`q = d` and leaves it unchanged otherwise. -/
abbrev d020Statement [Finite σ]
    (ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring)
    (q d : σ →₀ ℕ) (_hq : q.degree ≤ d.degree)
    (c : F.valuationSubring) : Prop :=
  MvPowerSeries.coeff q
      (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
        (H + MvPowerSeries.monomial d c)) =
    MvPowerSeries.coeff q
        (MvPowerSeries.subst (fun i : σ => inVariable ebar i) H) +
      if q = d then π ^ d.degree * c else 0

end Langlands.NYLL.PortInternal.M351

end
