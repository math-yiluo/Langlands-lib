/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 293, 2026-11-14: extract M353.006, M353.007 and M353.013
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709.
Move source-private declarations to stable Langlands.NYLL.PortInternal.M353
names and replace source imports by focused namespaced dependencies.
Preserve all definition bodies, with references renamed to the adapted declarations.
Record all adaptations in the paired Markdown. The original LICENSE and
NOTICE are retained in licenses/NYLL/.
Modified by Worker 293, 2026-11-16: import the published exact M352.003
proof from RecursiveCorrection.HasLinearTermProof.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.Approximation.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DegreeIndexList.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection.HasLinearTermProof

/-!
# Fixed-degree correction data
-/

noncomputable section

universe u v w

namespace Langlands.NYLL

open LocalFieldTheory.DiscreteValuationField
open LubinTate LubinTate.SameUniformizer

namespace PortInternal.M353

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {pi : F.valuationSubring}
variable {sigma : Type w} [Fintype sigma]

/-- One fixed-degree correction, bundled with preservation of the prescribed linear term. -/
noncomputable def d006
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (H : d002 (F := F) L)
    (d : {d : sigma →₀ ℕ // d.degree = m}) :
    d002 (F := F) L := by
  have hd : 2 ≤ d.1.degree := by
    simpa only [d.2] using hm
  exact
    ⟨correctedIntertwiner hpi e ebar H.2 d.1 hd,
      correctedIntertwiner_hasLinearTerm hpi e ebar H.2 d.1 hd⟩

/-- Apply fixed-degree corrections from left to right. -/
noncomputable def d007
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    {m : ℕ} (hm : 2 ≤ m)
    (ds : List {d : sigma →₀ ℕ // d.degree = m})
    (H : d002 (F := F) L) :
    d002 (F := F) L :=
  ds.foldl (d006 hpi e ebar hm) H

/-- Correct every monomial of a fixed total degree. -/
noncomputable def d013
    (hpi : F.toCompleteDVF.valuation.IsUniformizer (pi : K))
    (e ebar : LubinTateSeries F pi)
    {L : sigma → F.valuationSubring}
    (H : d002 (F := F) L)
    (m : ℕ) (hm : 2 ≤ m) :
    d002 (F := F) L :=
  d007 hpi e ebar hm (d003 (sigma := sigma) m) H

end PortInternal.M353
end Langlands.NYLL

end
