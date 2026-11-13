/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.Intermediate.Definitions
import Mathlib.GroupTheory.Complement

/-!
# NYLL chosen right transversal for transfer

Modified by Worker 196, 13 November 2026: extract M071.017 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean`,
lines 576–583, at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The private source definition is exposed as `Langlands.NYLL.PortInternal.M071.d017`.
The extension-subgroup abbreviation is expanded to its Mathlib defining term.
See the paired Markdown for the complete correspondence and modifications, and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

universe u

namespace Langlands.NYLL.PortInternal.M071

open ClassFormation

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A fixed choice of right-coset representatives for the intermediate subgroup in `K/L`. -/
def d017
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K).RightTransversal :=
  ⟨Set.range Quotient.out, Subgroup.isComplement_range_right Quotient.out_eq'⟩

end
end Langlands.NYLL.PortInternal.M071
