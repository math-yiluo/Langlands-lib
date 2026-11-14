/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 325, 14 November 2026: extract M353.037–039 as closed
Prop-valued definitions preserving their complete effective source telescopes;
use the planned PortInternal names and published focused definition imports.
The source proofs are omitted. See the paired Markdown and licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate
open Langlands.NYLL.LubinTate.SameUniformizer

-- Preserve the source hypothesis names inside the closed propositions.
set_option linter.unusedVariables false

/-- Target: a replacement at another index of the same degree preserves the defect coefficient. -/
def d037Statement.{u, v, w} : Prop :=
  ∀ {K : Type u} [Field K] {F : LocalField.{u, v} K}
    {pi : F.valuationSubring} {sigma : Type w} [Fintype sigma]
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : d002 (F := F) L)
    (q d : {d : sigma →₀ ℕ // d.degree = m})
    (hqd : q ≠ d),
    MvPowerSeries.coeff q.1
        (defect e ebar (d030 hm target H d).1) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1)

/-- Target: replacements avoiding a fixed same-degree index preserve its defect coefficient. -/
def d038Statement.{u, v, w} : Prop :=
  ∀ {K : Type u} [Field K] {F : LocalField.{u, v} K}
    {pi : F.valuationSubring} {sigma : Type w} [Fintype sigma]
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : d002 (F := F) L)
    (q : {d : sigma →₀ ℕ // d.degree = m})
    (hq : q ∉ ds),
    MvPowerSeries.coeff q.1
        (defect e ebar (d031 hm target ds H).1) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1)

/-- Target: the exact change of a defect coefficient at a member of a nodup replacement list. -/
def d039Statement.{u, v, w} : Prop :=
  ∀ {K : Type u} [Field K] {F : LocalField.{u, v} K}
    {pi : F.valuationSubring} {sigma : Type w} [Fintype sigma]
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : d002 (F := F) L)
    (hds : ds.Nodup)
    (q : {d : sigma →₀ ℕ // d.degree = m})
    (hq : q ∈ ds),
    MvPowerSeries.coeff q.1
        (defect e ebar (d031 hm target ds H).1) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1) +
        pi * ((1 - pi ^ (m - 1)) *
          (MvPowerSeries.coeff q.1 target -
            MvPowerSeries.coeff q.1 H.1))

end Langlands.NYLL.PortInternal.M353
