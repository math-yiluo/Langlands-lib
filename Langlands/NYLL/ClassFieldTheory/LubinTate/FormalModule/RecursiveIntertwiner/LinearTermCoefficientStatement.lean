/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 325, 14 November 2026: extract the type of source private
theorem M353.043 as a Prop-valued definition, give it the planned public
PortInternal.M353.d043Statement name, and quantify its complete effective
source telescope inside the proposition. Replace the source's broad imports
by the published LocalField and linear-term definitions. The source proof
is omitted. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate.SameUniformizer

/-- Target for the source private low-degree coefficient comparison M353.043. -/
def d043Statement.{u, v, w} : Prop :=
  ∀ {K : Type u} [Field K] {F : LocalField.{u, v} K}
    {sigma : Type w} [Fintype sigma]
    {H : MvPowerSeries sigma F.valuationSubring}
    {L : sigma → F.valuationSubring}
    (hH : HasLinearTerm H L)
    (d : sigma →₀ ℕ) (hd : d.degree < 2),
    MvPowerSeries.coeff d H =
      MvPowerSeries.coeff d (linearForm L)

end Langlands.NYLL.PortInternal.M353
