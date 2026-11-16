/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 773, 2026-11-16: extract the proof of M354.010
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix its namespace with Langlands.NYLL, replace the whole source
imports by focused published targets and proofs, and express the result
using its exact published proposition target. Add a change step exposing
that target's body; preserve the source telescope and subsequent proof.
Omit unrelated declarations, unused section settings and source opens.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U010.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup.SubstitutionClosure.U009.Proofs
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.InVariableHasSubst

/-!
# Intertwining under multivariable substitution

The exact proof of source unit M354.010, using composition of substitutions.
-/

universe u v w w'

namespace Langlands.NYLL.LubinTate.SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} {τ : Type w'}

namespace Intertwines

/-- An intertwiner remains an intertwiner after substituting a family of
intertwiners. -/
theorem subst
    [Finite σ] [Finite τ]
    {e ebar ehat : LubinTateSeries F π}
    {H : MvPowerSeries σ F.valuationSubring}
    (hH : Intertwines e ebar H)
    (hHsubst : PowerSeries.HasSubst H)
    {G : σ → MvPowerSeries τ F.valuationSubring}
    (hGsubst : MvPowerSeries.HasSubst G)
    (hG : ∀ i, Intertwines ebar ehat (G i)) :
    Intertwines.substStatement hH hHsubst hGsubst hG := by
  change Intertwines e ehat (MvPowerSeries.subst G H)
  rw [Intertwines] at hH ⊢
  calc
    PowerSeries.subst (MvPowerSeries.subst G H) e.toPowerSeries =
        MvPowerSeries.subst G
          (PowerSeries.subst H e.toPowerSeries) :=
      (subst_powerSeries_subst hHsubst hGsubst
        e.toPowerSeries).symm
    _ = MvPowerSeries.subst G
          (MvPowerSeries.subst
            (fun i : σ => inVariable ebar i) H) := by
      rw [hH]
    _ = MvPowerSeries.subst
          (fun i : σ =>
            MvPowerSeries.subst G (inVariable ebar i)) H :=
      MvPowerSeries.subst_comp_subst_apply
        (inVariable_hasSubst ebar) hGsubst H
    _ = MvPowerSeries.subst
          (fun i : σ =>
            PowerSeries.subst (G i) ebar.toPowerSeries) H := by
      congr 1
      funext i
      exact subst_inVariable ebar hGsubst i
    _ = MvPowerSeries.subst
          (fun i : σ =>
            MvPowerSeries.subst
              (fun j : τ => inVariable ehat j) (G i)) H := by
      congr 1
      funext i
      exact hG i
    _ = MvPowerSeries.subst
          (fun j : τ => inVariable ehat j)
          (MvPowerSeries.subst G H) :=
      (MvPowerSeries.subst_comp_subst_apply
        hGsubst (inVariable_hasSubst ehat) H).symm

end Intertwines

end Langlands.NYLL.LubinTate.SameUniformizer
