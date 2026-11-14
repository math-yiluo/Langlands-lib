/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-
Modified by Worker 640 on 2026-11-14: extracted the proof of M144.029
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

/-- Positive powers stay in a multiplicatively closed submodule. -/
theorem submodule_pow_succ_mem_of_mul_closed
    {E : Submodule 𝒪[K] L}
    (hmul : ∀ x : L, x ∈ E → ∀ y : L, y ∈ E → x * y ∈ E)
    {x : L} (hx : x ∈ E) :
    submodule_pow_succ_mem_of_mul_closedStatement (K := K) (L := L) hmul hx := by
  unfold submodule_pow_succ_mem_of_mul_closedStatement
  intro m
  induction m with
  | zero => simpa using hx
  | succ m ih =>
      have hmul_mem : x ^ (m + 1) * x ∈ E := hmul (x ^ (m + 1)) ih x hx
      simpa [pow_add, mul_assoc, mul_comm, mul_left_comm] using hmul_mem

end Langlands.NYLL.CyclicCohomology
