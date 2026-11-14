/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5424 (2026-11-14): extract only the proof of M113.017 from
Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean (lines 212–217; partition unit
lines 215–221)
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL. Import only
the published Basic.Statements module, state the theorem as its closed proposition
`sigmaMinusOne_mulStatement`, and introduce that proposition's eight binders before
the unchanged source `simp` call. The source `omit` line, section variables and
noncomputable section are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements

/-!
# The multiplicative coboundary `a ↦ a^(σ-1)` is multiplicative (NYLL M113.017)

For a group `G` acting on a commutative group `A` by multiplicative
automorphisms and `σ : G`, `(a * b)^(σ-1) = a^(σ-1) * b^(σ-1)`.
-/

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

/-- The multiplicative coboundary `a ↦ a^(σ-1)` is multiplicative. -/
theorem sigmaMinusOne_mul : sigmaMinusOne_mulStatement.{uG, uA} := by
  intro G A _ _ _ σ a b
  simp [sigmaMinusOne, mul_comm, mul_left_comm, mul_assoc]

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
