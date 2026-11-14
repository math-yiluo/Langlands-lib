/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 410, 2026-11-14: extract only M338.001 (lines 34–40)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix
the namespace with Langlands.NYLL, replace the original
CoefficientEquation import by the focused published LocalField
definition module and the two Mathlib modules the definition uses, omit
the section variables of line 32 (shadowed by the explicit parameters),
and focus the module documentation. The definition's name, explicit
parameters, type and body are unchanged. The original LICENSE and NOTICE
remain in licenses/NYLL/.
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.PowerSeries.Basic
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions

/-!
# The standard Lubin--Tate polynomial series

For an element `π` of the valuation subring of a local field, this module
defines the polynomial power series

`π X + X ^ q`,

where `q` is the cardinality of the residue field. No uniformizer
hypothesis is needed for the definition itself.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The polynomial power series `π X + X ^ q`, where `q` is the residue
field cardinality. -/
noncomputable def standardLubinTatePowerSeries
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    PowerSeries F.valuationSubring :=
  PowerSeries.C π * PowerSeries.X +
    PowerSeries.X ^ Nat.card F.residueField

end Langlands.NYLL.LubinTate

end
