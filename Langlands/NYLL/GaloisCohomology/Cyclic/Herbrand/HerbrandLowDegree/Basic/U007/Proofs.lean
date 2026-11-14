/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5424 (2026-11-14): extract only the proof of M113.007 from
Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean (lines 102–114, with the
M113.006 proof of lines 99–100; partition unit lines 108–120)
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL. Import only
the published Basic.Statements module and state the theorem as its closed
proposition `monoidHom_card_eq_card_range_mul_card_range_of_exactStatement`. The
source proof rewrites with M113.006 (`monoidHom_card_eq_card_ker_mul_card_range`)
for `g`, which is not yet in the Library; the two rewrites of its source proof
(lines 99–100) are inlined instead, so no declaration is added. The source
`omit` line, section variables and noncomputable section are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements

/-!
# Cardinality at an exact spot (NYLL M113.007)

If `f : X →* Y` and `g : Y →* Z` satisfy `range f = ker g` and `Y` is finite,
then `#Y = #range f * #range g`.
-/

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe uA uB uC

/-- Cardinality source for one exact spot of a group-hom sequence.  If
`range f = ker g`, then the middle group has cardinality
`#range(f) * #range(g)`. -/
theorem monoidHom_card_eq_card_range_mul_card_range_of_exact :
    monoidHom_card_eq_card_range_mul_card_range_of_exactStatement.{uA, uB, uC} := by
  intro X Y Z _ _ _ _ f g hexact
  -- Inlined source proof of M113.006 for `g`: `#Y = #ker g * #range g`.
  rw [← (MonoidHom.ker g).card_mul_index, Subgroup.index_ker, ← hexact]

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
