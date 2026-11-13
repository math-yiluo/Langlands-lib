/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.Restriction.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.Intermediate.Definitions

/-!
# NYLL intermediate quotient inclusion and image targets

Modified by Worker 196, 13 November 2026: extract `transferNormNaturalityIntermediateInclusion`, lines 36–45; `transferNormNaturalityIntermediateSubgroup`, lines 92–100; `transferNormNaturalityIntermediateInclusion_mk`, lines 52–61; `transferNormNaturalityIntermediateInclusion_injective`, lines 66–73 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransfer.lean` at `fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with
`Langlands.NYLL`, use focused imports and turn source theorems into Prop-valued
definitions without their proofs. See the paired Markdown for all changes and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

def transferNormNaturalityIntermediateInclusion_mkStatement
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    (k' : K'.toSubgroup) : Prop :=
    transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K
        (QuotientGroup.mk k') =
      QuotientGroup.mk (Subgroup.inclusion hK'K k')

def transferNormNaturalityIntermediateInclusion_injectiveStatement
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] : Prop :=
    Function.Injective
      (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)

end
end Langlands.NYLL.ClassFormation
