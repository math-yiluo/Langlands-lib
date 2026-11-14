/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5424 (2026-11-14): extract only the proof of M113.008 from
Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean (lines 116–124; partition unit
lines 121–131)
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL. Import only
the published Basic.Statements module, state the theorem as its closed proposition
`card_subgroupOf_eq_cardStatement`, and introduce that proposition's six binders
before the unchanged source term (turned into an `exact`). The source `omit` line,
section variables and noncomputable section are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements

/-!
# Cardinality of `H.subgroupOf K` (NYLL M113.008)

If `H ≤ K` are subgroups of a finite group, then `H` viewed as a subgroup of
`K` has the same cardinality as `H`.
-/

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe uA

/-- If `H ≤ K`, viewing `H` as a subgroup of `K` does not change its
cardinality. -/
theorem card_subgroupOf_eq_card : card_subgroupOf_eq_cardStatement.{uA} := by
  intro X _ _ H K hHK
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
