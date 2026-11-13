/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 126, 13 November 2026:
Prove M007.010 from Nyll/GaloisCohomology/ProfiniteIntegers/TopologicalGeneration.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing
its internal binders. The original proof applies the M007.009 theorem to
`QuotientGroup.mk' N`; because no M007.009 proof is published, its proof
steps at source lines 179-187 are inlined here, specialized to that
quotient map. Import only the TopologicalGeneration Statements module.
Omit all other source declarations. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.Statements

/-!
# Topological generation descends to quotients

A set that topologically generates a topological group has an image
that topologically generates its quotient by any normal subgroup.
-/

namespace Langlands.NYLL.ClassFormation

universe u

/-- Topological generation descends to a quotient by a normal subgroup. -/
theorem topologicallyGenerates_quotient_image :
    topologicallyGenerates_quotient_imageStatement.{u} := by
  intro G _ _ _ N _ X hX
  have hmap :
      (Subgroup.closure X).map (QuotientGroup.mk' N) =
        Subgroup.closure ((QuotientGroup.mk' N) '' X) :=
    MonoidHom.map_closure (QuotientGroup.mk' N) X
  have htop :
      ((Subgroup.closure X).map (QuotientGroup.mk' N)).topologicalClosure = ⊤ :=
    DenseRange.topologicalClosure_map_subgroup
      (f := QuotientGroup.mk' N) (hf := continuous_quotient_mk')
      (hf' := (QuotientGroup.mk'_surjective N).denseRange) hX
  rw [TopologicallyGenerates, ← hmap]
  exact htop

end Langlands.NYLL.ClassFormation
