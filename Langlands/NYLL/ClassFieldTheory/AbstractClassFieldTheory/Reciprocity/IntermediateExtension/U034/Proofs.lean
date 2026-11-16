/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U014.Proofs

/-!
# NYLL M076.034: intermediateSubgroup_map_quotient_eq

Modified by Worker 751: extract the source theorem at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, drop the unused `open KummerTheory`, and prove its published
named target from the focused statement import and the published proof of
M040.014 `extensionQuotientMk_surjective`. The paired Markdown records the
implemented proof and every adaptation. See `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- Mapping the inverse image of `S` back to `G(L/K)` recovers `S`
itself. -/
theorem intermediateSubgroup_map_quotient_eq {K : ClosedSubgroup G}
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    intermediateSubgroup_map_quotient_eqStatement L S :=
  Subgroup.map_comap_eq_self_of_surjective (f := L.extensionQuotientMk)
    (L.extensionQuotientMk_surjective) S

end FiniteGaloisSubextension
end Langlands.NYLL.ClassFormation
