/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.ExtensionSubgroupLe.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.U013.Proofs

/-!
# NYLL M076.003: `G_L` lies in every intermediate subgroup

Modified by Worker 756, 16 November 2026: extract the proof of M076.003
`FiniteGaloisSubextension.extensionSubgroup_le_intermediateSubgroup`
(lines 59–67) of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, and state the theorem as the published Statement applied to
the source parameters. The source's use of the unpublished M076.002
`mem_intermediateSubgroup_iff`, which holds by `Iff.rfl`, is replaced by a
definitional `change`; the published M040.013 `extensionQuotientMk_eq_one_iff`
is imported. The paired Markdown records every modification. See
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The original `G_L` lies in every inverse-image subgroup. -/
theorem extensionSubgroup_le_intermediateSubgroup
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    extensionSubgroup_le_intermediateSubgroupStatement L S := by
  intro x hx
  change L.extensionQuotientMk x ∈ S
  have hmk : L.extensionQuotientMk x = 1 :=
    (show L.extensionQuotientMk x = 1 ↔
        x ∈ extensionSubgroup K L.field L.below from
      L.extensionQuotientMk_eq_one_iff x).2 hx
  rw [hmk]
  exact S.one_mem

end FiniteGaloisSubextension

end

end Langlands.NYLL.ClassFormation
