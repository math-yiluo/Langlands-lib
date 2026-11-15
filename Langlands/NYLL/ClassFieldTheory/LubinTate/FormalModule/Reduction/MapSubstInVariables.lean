/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 465, 2026-11-15: extract the proof of M349.004
(`map_subst_inVariables`, source lines 94-108) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL; import the published Reduction statement module and the
published M348.003 proof module in place of the source imports; state the
theorem through its published Prop target `map_subst_inVariablesStatement`,
unfolded by a leading `show _ = _`; prove the M349.002 prerequisite
privately under a fresh name (repeating its source proof, lines 67-75) so
that this focused candidate does not import a proof still awaiting
publication; and replace the module documentation. The original LICENSE and
NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.Statements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.InVariableHasSubst

/-!
# Reduction of a series evaluated at inserted Lubin--Tate series

Proof of NYLL M349.004: reducing `H(ebar(X_i))_i` to the residue field gives
the expansion `Hbar(X_i ^ q)_i`, where `q` is the cardinality of the residue
field.
-/

noncomputable section

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- Reduction of `e(X_i)` is `X_i ^ q`; a private copy of the source proof of
M349.002. -/
private theorem map_inVariable_for_subst (e : LubinTateSeries F π) (i : σ) :
    MvPowerSeries.map F.residueMap (inVariable e i) =
      (MvPowerSeries.X i : MvPowerSeries σ F.residueField) ^
        Nat.card F.residueField := by
  have hX : PowerSeries.HasSubst
      (MvPowerSeries.X i : MvPowerSeries σ F.valuationSubring) :=
    PowerSeries.HasSubst.X i
  have hXbar : PowerSeries.HasSubst
      (MvPowerSeries.X i : MvPowerSeries σ F.residueField) :=
    PowerSeries.HasSubst.X i
  rw [inVariable, PowerSeries.map_subst hX e.toPowerSeries,
    e.map_residue_eq_frobenius, MvPowerSeries.map_X,
    PowerSeries.subst_pow hXbar, PowerSeries.subst_X hXbar]

/-- The reduced right side `H(ebar(X_i))` is the expansion
`Hbar(X_i ^ q)` (NYLL M349.004). -/
theorem map_subst_inVariables [Finite σ]
    (ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) :
    map_subst_inVariablesStatement ebar H := by
  show _ = _
  rw [MvPowerSeries.map_subst (inVariable_hasSubst ebar) H]
  simp_rw [map_inVariable_for_subst]
  rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]

end SameUniformizer
end Langlands.NYLL.LubinTate

end
