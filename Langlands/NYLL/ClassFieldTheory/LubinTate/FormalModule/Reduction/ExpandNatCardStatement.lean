/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 487, 2026-11-14: extract only the statement of the source
theorem M349.001 (`mvPowerSeries_expand_natCard`, source lines 32-38) from
upstream commit fbd320cd8b1b06487c58227e92eb135794267709 as the Prop-valued
target `mvPowerSeries_expand_natCardStatement`; prefix the namespace with
Langlands.NYLL; keep only the two Mathlib imports the statement needs; omit
the source proof, the other source declarations and the source
`noncomputable section`; replace the module documentation. The binders and
the conclusion are the source theorem's. The original LICENSE and NOTICE
remain in licenses/NYLL/.
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.RingTheory.MvPowerSeries.Expand

/-!
# Proposition target for multivariable finite-field Frobenius expansion

Exact proposition target for the first theorem of the source module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.Reduction`: over a finite
field `k`, replacing each variable of a multivariable power series by its
`Nat.card k`-th power gives the `Nat.card k`-th power of the series.
-/

universe u w

namespace Langlands.NYLL.LubinTate
namespace SameUniformizer

/-- Target of M349.001 (`mvPowerSeries_expand_natCard`): multivariable
finite-field Frobenius. Replacing each variable by its `q`th power, where
`q = Nat.card k`, is the same as taking the `q`th power of the whole
series. -/
abbrev mvPowerSeries_expand_natCardStatement
    {k : Type u} [Field k] [Finite k]
    {σ : Type w} [Finite σ] (f : MvPowerSeries σ k) : Prop :=
  MvPowerSeries.expand (Nat.card k) (Nat.ne_of_gt Nat.card_pos) f =
    f ^ Nat.card k

end SameUniformizer
end Langlands.NYLL.LubinTate
