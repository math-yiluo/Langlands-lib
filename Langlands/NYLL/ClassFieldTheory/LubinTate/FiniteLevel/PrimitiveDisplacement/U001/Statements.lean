/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299, 2026-11-13: extract the proposition of M362.001
from commit fbd320cd8b1b06487c58227e92eb135794267709, place the private
helper in Langlands.NYLL.PortInternal.M362, and replace the theorem
with its Prop-valued statement target. Reduce imports to Mathlib.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Coefficients after substituting `(X, 0)` -/

universe u

namespace Langlands.NYLL.PortInternal.M362

/-- NYLL M362.001: when the second exponent is zero, substituting `(X, 0)`
preserves the coefficient at the first exponent. -/
def d001Statement
    {R : Type u} [CommRing R]
    (f : MvPowerSeries (Fin 2) R) (d : Fin 2 →₀ ℕ)
    (_hd : d 1 = 0) : Prop :=
  PowerSeries.coeff (d 0)
      (MvPowerSeries.subst
        ![(PowerSeries.X : PowerSeries R), 0] f) =
    MvPowerSeries.coeff d f

end Langlands.NYLL.PortInternal.M362
