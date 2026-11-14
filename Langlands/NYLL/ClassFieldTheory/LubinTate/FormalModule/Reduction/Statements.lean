/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 487, 2026-11-14: extract the statements of the source
theorems M349.002-M349.006 (source lines 57-133) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued targets named
`<source name>Statement`; prefix the namespace with Langlands.NYLL; import
the published Intertwiner and LinearTerm definition modules and the Mathlib
expansion module in place of the source imports; omit the source proofs,
the separately stated M349.001 and the source `noncomputable section`;
underscore the hypothesis names that the conclusions do not mention; and
replace the module documentation. Each target keeps the source section
variables, `omit`/`[Finite σ]` instance changes, explicit and implicit
parameters, and has the source conclusion as its body. The original
LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.SetTheory.Cardinal.Finite
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions
import Mathlib.RingTheory.MvPowerSeries.Expand

/-!
# Proposition targets for the reduction of an intertwining defect

Exact proposition targets for the theorems M349.002-M349.006 of the source
module `Nyll.ClassFieldTheory.LubinTate.FormalModule.Reduction`. After
reduction to the finite residue field, a Lubin--Tate series becomes the
Frobenius power series `X ^ q`, so the two sides of the intertwining equation
both reduce to the `q`th power of the reduced series. Hence the defect
reduces to zero, and every coefficient of the defect is divisible by the
chosen uniformizer.
-/

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

omit [Fintype σ] in
/-- Target of M349.002 (`map_inVariable`): reduction of `e(X_i)` is
`X_i ^ q`. -/
abbrev map_inVariableStatement (e : LubinTateSeries F π) (i : σ) : Prop :=
  MvPowerSeries.map F.residueMap (inVariable e i) =
    (MvPowerSeries.X i : MvPowerSeries σ F.residueField) ^
      Nat.card F.residueField

/-- Target of M349.003 (`map_subst_lubinTateSeries`): the reduced left side
`e(H)` is `Hbar ^ q`. -/
abbrev map_subst_lubinTateSeriesStatement
    (e : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (_hH : HasLinearTerm H L) : Prop :=
  MvPowerSeries.map F.residueMap
      (PowerSeries.subst H e.toPowerSeries) =
    (MvPowerSeries.map F.residueMap H) ^
      Nat.card F.residueField

omit [Fintype σ] in
/-- Target of M349.004 (`map_subst_inVariables`): the reduced right side
`H(ebar(X_i))` is the expansion `Hbar(X_i ^ q)`. -/
abbrev map_subst_inVariablesStatement [Finite σ]
    (ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) : Prop :=
  MvPowerSeries.map F.residueMap
      (MvPowerSeries.subst
        (fun i : σ ↦ inVariable ebar i) H) =
    MvPowerSeries.expand (Nat.card F.residueField)
      (Nat.ne_of_gt Nat.card_pos)
      (MvPowerSeries.map F.residueMap H)

/-- Target of M349.005 (`map_defect_eq_zero`): the same-uniformizer
intertwining defect vanishes after reduction. -/
abbrev map_defect_eq_zeroStatement
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (_hH : HasLinearTerm H L) : Prop :=
  MvPowerSeries.map F.residueMap (defect e ebar H) = 0

/-- Target of M349.006 (`uniformizer_dvd_coeff_defect`): every coefficient
of the defect is divisible by the chosen uniformizer. -/
abbrev uniformizer_dvd_coeff_defectStatement
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (_hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) : Prop :=
  π ∣ MvPowerSeries.coeff d (defect e ebar H)

end SameUniformizer
end Langlands.NYLL.LubinTate
