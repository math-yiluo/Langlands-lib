/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 325, 14 November 2026: extract M353.041–042 as closed
Prop-valued definitions preserving their complete effective source telescopes;
use the planned PortInternal names and published focused definition imports.
The source proofs are omitted. See the paired Markdown and licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.ReplaceDegree
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate
open Langlands.NYLL.LubinTate.SameUniformizer

-- Preserve the source hypothesis names inside the closed propositions.
set_option linter.unusedVariables false

/-- Target: agreement below m extends through m after replacing all degree-m coefficients. -/
def d041Statement.{u, v, w} : Prop :=
  ∀ {K : Type u} [Field K] {F : LocalField.{u, v} K}
    {sigma : Type w} [Fintype sigma]
    {L : sigma → F.valuationSubring}
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : d002 (F := F) L)
    (m : ℕ) (hm : 2 ≤ m)
    (hlower : ∀ q : sigma →₀ ℕ, q.degree < m →
      MvPowerSeries.coeff q H.1 =
        MvPowerSeries.coeff q target)
    (q : sigma →₀ ℕ) (hq : q.degree ≤ m),
    MvPowerSeries.coeff q (d040 target H m hm).1 =
      MvPowerSeries.coeff q target

/-- Target: replacing degree m changes its defect coefficient by the exact scalar response. -/
def d042Statement.{u, v, w} : Prop :=
  ∀ {K : Type u} [Field K] {F : LocalField.{u, v} K}
    {pi : F.valuationSubring} {sigma : Type w} [Fintype sigma]
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : d002 (F := F) L)
    (m : ℕ) (hm : 2 ≤ m)
    (q : sigma →₀ ℕ) (hq : q.degree = m),
    MvPowerSeries.coeff q
        (defect e ebar (d040 target H m hm).1) =
      MvPowerSeries.coeff q (defect e ebar H.1) +
        pi * ((1 - pi ^ (m - 1)) *
          (MvPowerSeries.coeff q target -
            MvPowerSeries.coeff q H.1))

end Langlands.NYLL.PortInternal.M353
