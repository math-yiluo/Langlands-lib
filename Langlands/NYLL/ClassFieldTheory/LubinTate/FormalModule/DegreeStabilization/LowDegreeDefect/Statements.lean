/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 495, 2026-11-14: extract the signatures of the source
theorems M351.027-M351.030 (lines 829-941) of
Nyll/ClassFieldTheory/LubinTate/FormalModule/DegreeStabilization.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued
targets. The three source-private theorems are renamed
Langlands.NYLL.PortInternal.M351.d027Statement, d028Statement and
d029Statement; the public theorem becomes
Langlands.NYLL.LubinTate.SameUniformizer.two_le_order_defectStatement.
Section variables are written out as the source elaborates them; the
`omit [Fintype σ]` and `[Finite σ]` of M351.028 are kept. The source imports
are replaced by the published focused LinearTerm and Intertwiner definition
modules. Source proofs and the local classical decidability instance are
omitted. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions

/-!
# Targets: the defect of a linear form vanishes through degree one

Exact proposition targets for the four source theorems that end the module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization`: the
linear form as a finite sum of degree-one monomials, the vanishing of the
defect coefficients through total degree one for a finite sum of such
monomials and for the full linear form, and the bound `2 ≤ order` for the
defect of any series with a prescribed linear term.
-/

universe u v w

namespace Langlands.NYLL

open LubinTate LubinTate.SameUniformizer
open LocalFieldTheory.DiscreteValuationField

namespace PortInternal.M351

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- Target of M351.027 (source-private
`linearForm_eq_sum_monomial_stabilization`, line 829): the linear form
`∑ i, C (L i) * X i` equals the sum of the degree-one monomials
`monomial (single i 1) (L i)`. -/
abbrev d027Statement [Fintype σ] (L : σ → F.valuationSubring) : Prop :=
  linearForm L =
    ∑ i, MvPowerSeries.monomial
      (Finsupp.single i 1) (L i)

/-- Target of M351.028 (source-private
`coeff_defect_sum_linear_monomials_eq_zero`, line 842): for a finite variable
type, the defect of any finite sum of degree-one monomials has zero coefficient
in every total degree at most one. -/
abbrev d028Statement [Finite σ]
    (e ebar : LubinTateSeries F π)
    (L : σ → F.valuationSubring)
    (s : Finset σ) (q : σ →₀ ℕ) (_hq : q.degree ≤ 1) : Prop :=
  MvPowerSeries.coeff q
      (defect e ebar
        (∑ i ∈ s, MvPowerSeries.monomial
          (Finsupp.single i 1) (L i))) = 0

/-- Target of M351.029 (source-private
`coeff_defect_linearForm_eq_zero_of_degree_le_one`, line 890): the defect of a
linear form has zero coefficient in every total degree at most one. -/
abbrev d029Statement [Fintype σ]
    (e ebar : LubinTateSeries F π)
    (L : σ → F.valuationSubring)
    (q : σ →₀ ℕ) (_hq : q.degree ≤ 1) : Prop :=
  MvPowerSeries.coeff q (defect e ebar (linearForm L)) = 0

end PortInternal.M351

namespace LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- Target of M351.030 (`two_le_order_defect`, line 902): the
same-uniformizer defect of a series with prescribed linear term has no
constant or linear coefficient, that is, total order at least two. -/
abbrev two_le_order_defectStatement
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (_hH : HasLinearTerm H L) : Prop :=
  (2 : ℕ∞) ≤ (defect e ebar H).order

end LubinTate.SameUniformizer

end Langlands.NYLL
