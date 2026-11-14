/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5424 (2026-11-14): extract only the proof of M113.016 from
Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean (lines 205–210; partition unit
lines 207–214)
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL. Import only
the published Basic.Statements module, state the theorem as its closed proposition
`map_sigmaMinusOneStatement`, and introduce that proposition's twelve binders
before the unchanged source `simp` call. The source `omit` line, section
variables and noncomputable section are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements

/-!
# Equivariant homomorphisms commute with `σ - 1` (NYLL M113.016)

If `f : A →* B` satisfies `f (g • a) = g • f a`, then
`f (a^(σ-1)) = (f a)^(σ-1)`.
-/

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA uB

/-- An equivariant homomorphism commutes with the sigma-minus-one operator. -/
theorem map_sigmaMinusOne : map_sigmaMinusOneStatement.{uG, uA, uB} := by
  intro G A B _ _ _ _ _ f hf σ a
  simp [sigmaMinusOne, hf σ a]

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
