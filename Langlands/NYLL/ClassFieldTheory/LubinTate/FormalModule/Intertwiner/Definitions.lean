/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 126, 2026-11-13: extract only the definitions M348.001,
M348.004 and M348.005 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, replace the original Series and LinearTerm imports by the
published focused Series definition module and Mathlib's power-series
substitution module, omit the four source theorems (published separately as
Prop targets and proofs), and extend the module documentation. The three
definition bodies and types are unchanged. The original LICENSE and NOTICE
remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.Definitions
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Intertwining equations for Lubin--Tate series

For two Lubin--Tate series with the same prescribed linear coefficient, this
module defines the insertion of a one-variable series into a chosen variable,
the multivariable intertwining equation and its additive defect.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type*}

/-- Insert a one-variable Lubin--Tate series into the variable `X_i`. -/
noncomputable def inVariable (e : LubinTateSeries F π) (i : σ) :
    MvPowerSeries σ F.valuationSubring :=
  PowerSeries.subst (MvPowerSeries.X i) e.toPowerSeries

/-- The literal same-uniformizer equation
`e(H(X_i)) = H(ebar(X_i))`. -/
def Intertwines (e ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) : Prop :=
  PowerSeries.subst H e.toPowerSeries =
    MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H

/-- The coefficientwise defect whose vanishing is the intertwining
equation. -/
noncomputable def defect (e ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) :
    MvPowerSeries σ F.valuationSubring :=
  PowerSeries.subst H e.toPowerSeries -
    MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H

end SameUniformizer
end Langlands.NYLL.LubinTate

end
