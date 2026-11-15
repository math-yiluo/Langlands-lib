/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.IntermediateExtension.Definitions

/-!
# Target: `G_L` lies in every intermediate subgroup

Modified by Worker 5264, 15 November 2026: state the source theorem M076.003
`extensionSubgroup_le_intermediateSubgroup` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, omit the proof and the unused `open KummerTheory`, and write
the section variables without `[IsTopologicalGroup G]`, which the source
omits for this theorem. See the paired Markdown and `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- Target: the original `G_L` lies in every inverse-image subgroup. -/
def extensionSubgroup_le_intermediateSubgroupStatement
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) : Prop :=
    extensionSubgroup K L.field L.below ≤ L.intermediateSubgroup S

end FiniteGaloisSubextension

end

end Langlands.NYLL.ClassFormation
