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

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Approximation.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Replacement.LinearTermProof

noncomputable section

universe u v w

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {sigma : Type w} [Fintype sigma]

/-- Replace one coefficient in a fixed total degree by the corresponding
coefficient of a target series. -/
noncomputable def d030
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (H : d002 (F := F) L)
    (d : {d : sigma →₀ ℕ // d.degree = m}) :
    d002 (F := F) L :=
  ⟨H.1 + MvPowerSeries.monomial d.1
      (MvPowerSeries.coeff d.1 target -
        MvPowerSeries.coeff d.1 H.1),
    d029 H.2 d.1 (by omega)
      (MvPowerSeries.coeff d.1 target -
        MvPowerSeries.coeff d.1 H.1)⟩

/-- Replace the coefficients indexed by a list in a fixed total degree. -/
noncomputable def d031
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (target : MvPowerSeries sigma F.valuationSubring)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : d002 (F := F) L) :
    d002 (F := F) L :=
  ds.foldl (d030 hm target) H

end Langlands.NYLL.PortInternal.M353
