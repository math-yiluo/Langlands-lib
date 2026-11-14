/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5424 (2026-11-14): extract only the proof of M113.010 from
Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean (lines 154–159; partition unit
lines 155–163)
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL. Import only
the published Basic.Statements module, state the theorem as its closed proposition
`map_tateNormStatement`, and introduce that proposition's twelve binders before
the unchanged source proof. The source section variables and noncomputable
section are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements

/-!
# Equivariant homomorphisms commute with the Tate norm (NYLL M113.010)

If `f : A →* B` satisfies `f (g • a) = g • f a`, then
`f (N_G a) = N_G (f a)`.
-/

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA uB

/-- An equivariant homomorphism commutes with the Tate norm. -/
theorem map_tateNorm : map_tateNormStatement.{uG, uA, uB} := by
  intro G A B _ _ _ _ _ _ f hf a
  simp only [tateNorm, map_prod]
  exact Finset.prod_congr rfl (fun g _hg => hf g a)

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
