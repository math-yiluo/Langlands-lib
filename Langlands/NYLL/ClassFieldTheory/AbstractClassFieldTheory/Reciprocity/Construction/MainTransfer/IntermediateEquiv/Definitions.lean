/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.Intermediate.U003.Proofs

/-!
# NYLL intermediate quotient equivalence onto its image

Modified by Worker 196, 13 November 2026: extract M071.005, lines 102–117,
from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace with
`Langlands.NYLL`, use the focused published injectivity proof import, and expand
`extensionSubgroup` to its Mathlib definition. Keep the entire source construction,
including its proof terms. See the paired Markdown and `licenses/NYLL/`.
-/

namespace Langlands.NYLL.ClassFormation

universe u
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The canonical identification of `G(L/K')` with its image in
`G(L/K)`. -/
noncomputable def transferNormNaturalityIntermediateQuotientEquiv
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) ≃*
      transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K :=
  MulEquiv.ofBijective
    (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K).rangeRestrict
    ⟨fun _ _ h =>
        transferNormNaturalityIntermediateInclusion_injective K K' L hLK' hK'K
          (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

end Langlands.NYLL.ClassFormation
