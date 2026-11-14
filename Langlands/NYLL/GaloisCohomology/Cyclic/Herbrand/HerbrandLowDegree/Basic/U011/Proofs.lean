/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5424 (2026-11-14): extract only the proof of M113.011 from
Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean (lines 161–173; partition unit
lines 164–178)
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL. Import only
the published Basic.Statements module, state the theorem as its closed proposition
`tateNorm_mulStatement`, and introduce that proposition's eight binders before the
unchanged source calc proof. The source `omit` line, section variables and
noncomputable section are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements

/-!
# The Tate norm is multiplicative (NYLL M113.011)

For a finite group `G` acting on a commutative group `A` by multiplicative
automorphisms, `N_G (a * b) = N_G a * N_G b`.
-/

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

/-- The finite-group norm is multiplicative. -/
theorem tateNorm_mul : tateNorm_mulStatement.{uG, uA} := by
  intro G A _ _ _ _ a b
  calc
    tateNorm G A (a * b) = ∏ g : G, (g • a) * (g • b) := by
      unfold tateNorm
      apply Finset.prod_congr rfl
      intro g _hg
      exact MulDistribMulAction.smul_mul g a b
    _ = tateNorm G A a * tateNorm G A b := by
      simp only [tateNorm, Finset.prod_mul_distrib]

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
