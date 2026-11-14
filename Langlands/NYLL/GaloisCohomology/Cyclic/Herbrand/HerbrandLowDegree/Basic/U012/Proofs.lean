/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5424 (2026-11-14): extract only the proof of M113.012 from
Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean (lines 175–181; partition unit
lines 179–185)
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL. Import only
the published Basic.Statements module, state the theorem as its closed proposition
`tateNorm_oneStatement`, and introduce that proposition's six binders before the
unchanged source proof. The source `@[simp]` attribute is dropped (the closed
proposition is not an equation, so it cannot serve as a simp lemma); the source
`omit` line, section variables and noncomputable section are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements

/-!
# The Tate norm of the identity (NYLL M113.012)

For a finite group `G` acting on a commutative group `A` by multiplicative
automorphisms, `N_G 1 = 1`.
-/

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

/-- The Tate norm of the identity is the identity. -/
theorem tateNorm_one : tateNorm_oneStatement.{uG, uA} := by
  intro G A _ _ _ _
  unfold tateNorm
  exact Finset.prod_eq_one (fun g _hg => MulDistribMulAction.smul_one g)

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
