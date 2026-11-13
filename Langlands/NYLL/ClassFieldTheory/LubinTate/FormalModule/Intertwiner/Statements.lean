/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 126, 2026-11-13: extract the statements of the source
theorems M348.002, M348.003, M348.006 and M348.007 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued targets named
`<source name>Statement`; prefix the namespace with Langlands.NYLL and
import the published M348 definition module. Each target keeps the source
section variables, explicit parameters and `[Finite σ]` hypotheses and has
the source conclusion as its body. The targets are reducible (`abbrev`) so
that the later proof of M348.002 can carry the source `@[simp]` attribute and
the proofs can be used by `simp` and `simp only` like the source theorems.
Source proofs are omitted. The original LICENSE and NOTICE remain in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions

/-!
# Proposition targets for the elementary intertwining laws

Exact proposition targets for the four theorems of the source module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.Intertwiner`: the inserted
series has zero constant coefficient, the inserted family admits
multivariable substitution over a finite variable type, intertwining is
vanishing of the defect, and each variable intertwines a series with itself.
-/

universe u v

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type*}

/-- Target of M348.002 (`constantCoeff_inVariable`): the series `e(X_i)` has
zero constant coefficient. -/
abbrev constantCoeff_inVariableStatement (e : LubinTateSeries F π) (i : σ) :
    Prop :=
  MvPowerSeries.constantCoeff (inVariable e i) = 0

/-- Target of M348.003 (`inVariable_hasSubst`): for a finite variable type,
the family `i ↦ e(X_i)` admits multivariable substitution. -/
abbrev inVariable_hasSubstStatement [Finite σ] (e : LubinTateSeries F π) :
    Prop :=
  MvPowerSeries.HasSubst (fun i : σ ↦ inVariable e i)

/-- Target of M348.006 (`intertwines_iff_defect_eq_zero`): the intertwining
equation holds exactly when its defect vanishes. -/
abbrev intertwines_iff_defect_eq_zeroStatement
    (e ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring) : Prop :=
  Intertwines e ebar H ↔ defect e ebar H = 0

/-- Target of M348.007 (`intertwines_X`): for a finite variable type, each
variable intertwines a Lubin--Tate series with itself. -/
abbrev intertwines_XStatement [Finite σ]
    (e : LubinTateSeries F π) (i : σ) : Prop :=
  Intertwines e e (MvPowerSeries.X i)

end SameUniformizer
end Langlands.NYLL.LubinTate
