/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 465, 2026-11-15: extract the proof of M349.002
(`map_inVariable`, source lines 61-75) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL; import the published Reduction statement module in place of
the source imports; state the theorem through its published Prop target
`map_inVariableStatement`, unfolded by a leading `show _ = _`; and replace
the module documentation. The rest of the source proof is unchanged. The original LICENSE and NOTICE remain in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.Statements

/-!
# Reduction of an inserted Lubin--Tate series

Proof of NYLL M349.002: reducing `e(X_i)` to the residue field gives
`X_i ^ q`, where `q` is the cardinality of the residue field.
-/

noncomputable section

universe u v w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w}

/-- Reduction of `e(X_i)` is `X_i ^ q` (NYLL M349.002). -/
theorem map_inVariable (e : LubinTateSeries F π) (i : σ) :
    map_inVariableStatement e i := by
  show _ = _
  have hX : PowerSeries.HasSubst
      (MvPowerSeries.X i : MvPowerSeries σ F.valuationSubring) :=
    PowerSeries.HasSubst.X i
  have hXbar : PowerSeries.HasSubst
      (MvPowerSeries.X i : MvPowerSeries σ F.residueField) :=
    PowerSeries.HasSubst.X i
  rw [inVariable, PowerSeries.map_subst hX e.toPowerSeries,
    e.map_residue_eq_frobenius, MvPowerSeries.map_X,
    PowerSeries.subst_pow hXbar, PowerSeries.subst_X hXbar]

end SameUniformizer
end Langlands.NYLL.LubinTate

end
