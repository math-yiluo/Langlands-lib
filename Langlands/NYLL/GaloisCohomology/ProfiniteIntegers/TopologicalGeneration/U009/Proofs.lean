/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 125, 13 November 2026 UTC:
Extract only the proof of M007.009 from
Nyll/GaloisCohomology/ProfiniteIntegers/TopologicalGeneration.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published TopologicalGeneration
Statements module. Prove its closed proposition by introducing all
eleven internal binders before retaining the original route through
MonoidHom.map_closure and DenseRange.topologicalClosure_map_subgroup
with hfsurj.denseRange. The section variables G, its instances and the
universes u and v become the binders of the closed proposition. Other
source declarations are omitted. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.Statements

/-!
# Topological generation along a continuous surjective homomorphism

The exact proof of the published closed assertion: the image of a
topologically generating set under a continuous surjective group
homomorphism topologically generates the target group.
-/

namespace Langlands.NYLL.ClassFormation

open Set
open scoped Topology Pointwise

universe u v

/-- Topological generation pushes forward along a continuous surjective
homomorphism. -/
theorem topologicallyGenerates_image_of_continuousSurjective :
    topologicallyGenerates_image_of_continuousSurjectiveStatement.{u, v} := by
  intro G _ _ _ H _ _ _ f hf hfsurj X hX
  have hmap :
      (Subgroup.closure X).map f = Subgroup.closure (f '' X) := by
    simpa using MonoidHom.map_closure f X
  have htop :
      ((Subgroup.closure X).map f).topologicalClosure = ⊤ := by
    exact DenseRange.topologicalClosure_map_subgroup
      (f := f) (hf := hf) (hf' := hfsurj.denseRange)
      (by simpa [TopologicallyGenerates] using hX)
  rw [TopologicallyGenerates, ← hmap]
  exact htop

end Langlands.NYLL.ClassFormation
