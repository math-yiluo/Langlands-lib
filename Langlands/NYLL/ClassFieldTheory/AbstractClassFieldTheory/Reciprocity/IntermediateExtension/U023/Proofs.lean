/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Statements

/-!
# NYLL M076.023: intermediateSubgroup_normal

Modified by Worker 751: extract the source theorem at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, drop the unused `open KummerTheory` and the redundant local
instance `let : S.Normal := hS`, and prove its published named target using
the focused statement import. The paired Markdown records the implemented
proof and every adaptation. See `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- A normal subgroup `S ◁ G(L/K)` has normal inverse image in `G_K`. -/
theorem intermediateSubgroup_normal {K : ClosedSubgroup G}
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (hS : S.Normal) : intermediateSubgroup_normalStatement L S hS :=
  hS.comap L.extensionQuotientMk

end FiniteGaloisSubextension
end Langlands.NYLL.ClassFormation
