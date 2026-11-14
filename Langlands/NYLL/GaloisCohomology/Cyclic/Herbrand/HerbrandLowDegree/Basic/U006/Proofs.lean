/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5424 (2026-11-14): extract only the proof of M113.006 from
Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean (lines 90–100; partition unit
lines 96–107)
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL. Import only
the published Basic.Statements module, state the theorem as its closed proposition
`monoidHom_card_eq_card_ker_mul_card_rangeStatement`, and introduce that
proposition's six binders before the unchanged source rewrite. The source
`omit` line, section variables and noncomputable section are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements

/-!
# Cardinality of the source of a homomorphism (NYLL M113.006)

For a group homomorphism `f : X →* Y` with `X` finite,
`#X = #ker f * #range f`.
-/

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe uA uB

/-- First-isomorphism cardinality source for finite exactness calculations:
the cardinality of the source of a group homomorphism is the product of the
cardinalities of its kernel and range. -/
theorem monoidHom_card_eq_card_ker_mul_card_range :
    monoidHom_card_eq_card_ker_mul_card_rangeStatement.{uA, uB} := by
  intro X Y _ _ _ f
  rw [← (MonoidHom.ker f).card_mul_index,
    Subgroup.index_ker]

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
