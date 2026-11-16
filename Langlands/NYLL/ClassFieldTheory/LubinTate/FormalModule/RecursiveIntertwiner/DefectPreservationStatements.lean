/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 293, 2026-11-14: extract M353.010, M353.011
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709.
Move source-private declarations to stable Langlands.NYLL.PortInternal.M353
names and replace source imports by focused namespaced dependencies.
Replace the source theorems by Prop-valued Statement definitions, preserving
their parameters and conclusions; the proofs are separate successors.
Record all adaptations in the paired Markdown. The original LICENSE and
NOTICE are retained in licenses/NYLL/.
Modified by Worker 293, 2026-11-16: disable the unused-variable linter
within this file to keep all original hypothesis names in proposition targets.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.CorrectionData
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Intertwiner.Definitions

/-!
# Same-degree defect preservation targets
-/

noncomputable section

set_option linter.unusedVariables false

universe u v w

namespace Langlands.NYLL

open LocalFieldTheory.DiscreteValuationField
open LubinTate LubinTate.SameUniformizer

namespace PortInternal.M353

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {pi : F.valuationSubring}
variable {sigma : Type w} [Fintype sigma]

/-- Exact target for source M353.010. -/
def d010Statement
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (H : d002 (F := F) L)
    (q d : {d : sigma →₀ ℕ // d.degree = m})
    (hqd : q ≠ d) : Prop :=
    MvPowerSeries.coeff q.1
        (defect e ebar (d006 hpi e ebar hm H d).1) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1)

/-- Exact target for source M353.011. -/
def d011Statement
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : d002 (F := F) L)
    (q : {d : sigma →₀ ℕ // d.degree = m})
    (hq : q ∉ ds) : Prop :=
    MvPowerSeries.coeff q.1
        (defect e ebar (d007 hpi e ebar hm ds H).1) =
      MvPowerSeries.coeff q.1 (defect e ebar H.1)

end PortInternal.M353
end Langlands.NYLL

end
