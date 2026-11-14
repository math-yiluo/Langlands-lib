/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 294, 2026-11-14: focused extraction of the indicated
M353 source units, namespace qualification, source-private name adaptation,
and replacement of the recursive imports by focused published dependencies.
The accompanying Markdown records exact source correspondence and edits.
License and notices are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.Definitions

universe u v w

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {sigma : Type w} [Fintype sigma]

set_option linter.unusedVariables false in
abbrev d032Statement
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : d002 (F := F) L)
    (d : {d : sigma →₀ ℕ // d.degree = m}) : Prop :=
    MvPowerSeries.coeff d.1 (d030 hm target H d).1 =
      MvPowerSeries.coeff d.1 target

set_option linter.unusedVariables false in
abbrev d033Statement
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : d002 (F := F) L)
    (q d : {d : sigma →₀ ℕ // d.degree = m})
    (hqd : q ≠ d) : Prop :=
    MvPowerSeries.coeff q.1 (d030 hm target H d).1 =
      MvPowerSeries.coeff q.1 H.1


end Langlands.NYLL.PortInternal.M353
