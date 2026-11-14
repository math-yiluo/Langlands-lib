/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 488, 2026-11-14: extract the statements of the source
theorems M351.002 (private `truncTotal_powerSeries_subst_eq_of_truncTotal_eq`,
source lines 72–80), M351.003 (private
`truncTotal_inVariables_subst_eq_of_truncTotal_eq`, lines 109–115) and
M351.004 (`coeff_defect_eq_of_coeff_eq_degree_le`, lines 135–153) of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean from
upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued
targets. The two source-private theorems become
Langlands.NYLL.PortInternal.M351.d002Statement and d003Statement; the public
theorem becomes
Langlands.NYLL.LubinTate.SameUniformizer.coeff_defect_eq_of_coeff_eq_degree_leStatement.
Each target keeps the source section variables used by the theorem, its
`[Finite σ]` hypothesis (the section `[Fintype σ]` is omitted, as by the
source `omit [Fintype σ] in`), its other binders in source order and its
conclusion. Replace the source imports by the published M348 definition
module and Mathlib's total-degree truncation module; omit the source
`noncomputable section`, `open scoped BigOperators` and the source proofs.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-!
# Proposition targets for finite-degree continuity of intertwining defects

Exact proposition targets for three theorems of the source module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`:

* (M351.002, source-private) total-degree truncation at `k` of
  `e(H)` depends only on the truncation at `k` of `H`, for `H` with zero
  constant coefficient;
* (M351.003, source-private) total-degree truncation at `k` of
  `H(ebar(X_i))_i` depends only on the truncation at `k` of `H`;
* (M351.004) agreement of the coefficients of `H` and `H'` in every total
  degree at most `m` makes the coefficients of their intertwining defects
  agree in every total degree at most `m`.
-/

attribute [local instance] Classical.propDecidable

universe u v w

namespace Langlands.NYLL.PortInternal.M351

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate
open Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

set_option linter.unusedVariables false in
/-- Target of M351.002 (source-private
`LubinTate.SameUniformizer.truncTotal_powerSeries_subst_eq_of_truncTotal_eq`):
if `H` and `H'` have zero constant coefficient and the same total-degree
truncation at `k`, then so do `e(H)` and `e(H')`. -/
abbrev d002Statement [Finite σ]
    (e : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (hH' : MvPowerSeries.constantCoeff H' = 0)
    {k : ℕ} (htrunc : H.truncTotal k = H'.truncTotal k) : Prop :=
  (PowerSeries.subst H e.toPowerSeries).truncTotal k =
    (PowerSeries.subst H' e.toPowerSeries).truncTotal k

set_option linter.unusedVariables false in
/-- Target of M351.003 (source-private
`LubinTate.SameUniformizer.truncTotal_inVariables_subst_eq_of_truncTotal_eq`):
if `H` and `H'` have the same total-degree truncation at `k`, then so do
`H(ebar(X_i))_i` and `H'(ebar(X_i))_i`. -/
abbrev d003Statement [Finite σ]
    (ebar : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    {k : ℕ} (htrunc : H.truncTotal k = H'.truncTotal k) : Prop :=
  (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H).truncTotal k =
    (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H').truncTotal k

end Langlands.NYLL.PortInternal.M351

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

set_option linter.unusedVariables false in
/-- Target of M351.004 (`coeff_defect_eq_of_coeff_eq_degree_le`): the
coefficient in total degree at most `m` of the same-uniformizer intertwining
defect depends only on the coefficients of the proposed intertwiner through
total degree `m`, for intertwiners with zero constant coefficient. -/
abbrev coeff_defect_eq_of_coeff_eq_degree_leStatement [Finite σ]
    (e ebar : LubinTateSeries F π)
    {H H' : MvPowerSeries σ F.valuationSubring}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (hH' : MvPowerSeries.constantCoeff H' = 0)
    {m : ℕ}
    (hcoeff : ∀ q : σ →₀ ℕ, q.degree ≤ m →
      MvPowerSeries.coeff q H = MvPowerSeries.coeff q H')
    {d : σ →₀ ℕ} (hd : d.degree ≤ m) : Prop :=
  MvPowerSeries.coeff d (defect e ebar H) =
    MvPowerSeries.coeff d (defect e ebar H')

end SameUniformizer
end Langlands.NYLL.LubinTate
