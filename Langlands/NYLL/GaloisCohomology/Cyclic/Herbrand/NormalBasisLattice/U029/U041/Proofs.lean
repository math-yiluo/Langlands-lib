/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-
Modified by Worker 640 on 2026-11-14: extracted the proof of M144.041
from NormalBasisLattice.lean at fbd320cd8b1b06487c58227e92eb135794267709,
prefixed the namespace with Langlands.NYLL, reduced imports, and stated the
result using the published proposition target. Local prerequisite adaptations
are documented in the paired Markdown. LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U029.Statements

namespace Langlands.NYLL.CyclicCohomology

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [ValuativeRel K]

/-- A closed submodule contains the limit of any convergent sequence in it. -/
theorem submodule_mem_of_tendsto_of_forall_mem_of_closed
    [TopologicalSpace L] {E : Submodule 𝒪[K] L} {f : Nat → L} {x : L}
    (hclosed : IsClosed (E : Set L)) (hf : Tendsto f atTop (nhds x))
    (hmem : ∀ d : Nat, f d ∈ E) :
    submodule_mem_of_tendsto_of_forall_mem_of_closedStatement
      (K := K) (L := L) hclosed hf hmem := by
  unfold submodule_mem_of_tendsto_of_forall_mem_of_closedStatement
  exact hclosed.mem_of_tendsto hf (Eventually.of_forall hmem)

end Langlands.NYLL.CyclicCohomology
