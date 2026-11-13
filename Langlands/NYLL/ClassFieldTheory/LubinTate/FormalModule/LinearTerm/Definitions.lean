/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 342 on 2026-11-13: extracted M347.001 and M347.003,
prefixed the namespace with Langlands.NYLL, and omitted the unused
PowerSeries.Substitution import and the source theorem declarations.
Definition bodies and parameter binding are unchanged. Details are in the
paired Markdown; LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# Prescribed linear terms for multivariable power series

A multivariable power series has a prescribed linear term when its difference
from the corresponding linear form has total order at least two.
-/

noncomputable section

namespace Langlands.NYLL.LubinTate.SameUniformizer

variable {R : Type*} [CommRing R]
variable {σ : Type*} [Fintype σ]

/-- The multivariable linear form `sum_i L_i X_i`. -/
noncomputable def linearForm (L : σ → R) : MvPowerSeries σ R :=
  ∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i

/-- A series has prescribed linear term `L` when its difference from
`sum_i L_i X_i` has total order at least two. -/
def HasLinearTerm (H : MvPowerSeries σ R) (L : σ → R) : Prop :=
  (2 : ℕ∞) ≤ (H - linearForm L).order

end Langlands.NYLL.LubinTate.SameUniformizer

end
