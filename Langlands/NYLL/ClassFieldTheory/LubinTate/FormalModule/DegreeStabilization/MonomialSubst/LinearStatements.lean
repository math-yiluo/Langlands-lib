/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 493, 2026-11-14: extract the propositions of the source
private theorems M351.017 and M351.018 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued targets
`Langlands.NYLL.PortInternal.M351.d017Statement` and `d018Statement`; replace
the source-private `linearInVariableStabilization` by its published port
`Langlands.NYLL.PortInternal.M351.d011`; open the Langlands.NYLL namespaces of
the published LocalField, LubinTateSeries and inVariable; import only the
published linear-model, Intertwiner definition and Mathlib order modules; and
omit the proofs. The section variables, the source `omit [Fintype σ]` with
the `[Finite σ]` premise of M351.017, all explicit parameters and the local
classical decidability instance are retained. The targets are reducible
(`abbrev`). The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization.LinearModel.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions
import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# A monomial substituted into Lubin--Tate variables and into their linear model

Proposition targets for two source-private theorems of
`Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`.
Substituting `X_i ↦ ebar(X_i)` and `X_i ↦ π X_i` into the monomial `c X^d`
gives series that agree below total degree `|d| + 1`; and the substitution
`X_i ↦ π X_i` sends `c X^d` to `π^|d| c X^d`.
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

/-- Target of M351.017 (source
`degree_add_one_le_order_subst_monomial_sub_linear_stabilization`): for a
finite variable type, substituting `X_i ↦ ebar(X_i)` and `X_i ↦ π X_i` into
the monomial `c X^d` gives series whose difference has order at least
`d.degree + 1`. -/
abbrev d017Statement [Finite σ]
    (ebar : LubinTateSeries F π)
    (d : σ →₀ ℕ) (c : F.valuationSubring) : Prop :=
  ((d.degree + 1 : ℕ) : ℕ∞) ≤
    (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
        (MvPowerSeries.monomial d c) -
      MvPowerSeries.subst
        (d011 (σ := σ) π)
        (MvPowerSeries.monomial d c)).order

/-- Target of M351.018 (source
`coeff_subst_linearInVariableStabilization_monomial`): substituting
`X_i ↦ π X_i` into the monomial `c X^d` gives a series whose coefficient at
`q` is `π ^ d.degree * c` when `q = d` and zero otherwise. -/
abbrev d018Statement
    (q d : σ →₀ ℕ) (c : F.valuationSubring) : Prop :=
  MvPowerSeries.coeff q
      (MvPowerSeries.subst
        (d011 (σ := σ) π)
        (MvPowerSeries.monomial d c)) =
    if q = d then π ^ d.degree * c else 0

end Langlands.NYLL.PortInternal.M351

end
