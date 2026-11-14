/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-
Modified by Worker 640 on 2026-11-14: extracted the proof of M144.032
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

variable (L : Type u) [Field L]

/-- Expand the inverse-correction partial sum at a successor. -/
theorem inverseCorrectionPartialSum_succ (x : L) (d : Nat) :
    inverseCorrectionPartialSum_succStatement (L := L) x d := by
  unfold inverseCorrectionPartialSum_succStatement
  simp [inverseCorrectionPartialSum, Finset.sum_range_succ]

end Langlands.NYLL.CyclicCohomology
