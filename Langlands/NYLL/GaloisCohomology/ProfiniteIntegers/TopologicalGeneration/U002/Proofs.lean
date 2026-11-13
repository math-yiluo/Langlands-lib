/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 13 November 2026:
Extract the proof of M007.002 from
Nyll/GaloisCohomology/ProfiniteIntegers/TopologicalGeneration.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing
its five internal binders, then following the original rewrite chain
unchanged. Import only the TopologicalGeneration Statements module. Omit
the source section variables and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.Statements

/-!
# Topological generation as density

A set topologically generates a topological group exactly when the
abstract subgroup it generates is dense.
-/

namespace Langlands.NYLL.ClassFormation

open Set
open scoped Topology Pointwise

universe u

/-- Topological generation is equivalently density of the generated abstract
subgroup. -/
theorem topologicallyGenerates_iff_dense :
    topologicallyGenerates_iff_denseStatement.{u} := by
  intro G _ _ _ X
  rw [TopologicallyGenerates, SetLike.ext'_iff, Subgroup.topologicalClosure_coe,
    Subgroup.coe_top, dense_iff_closure_eq]

end Langlands.NYLL.ClassFormation
