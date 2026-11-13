/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.Restriction.Definitions

/-!
# NYLL intermediate quotient inclusion and image data

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

def transferNormNaturalityIntermediateInclusion
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) →*
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
  finiteReciprocityNaturalityRestriction K K' L L (hLK'.trans hK'K) hLK'
    hK'K le_rfl

def transferNormNaturalityIntermediateSubgroup
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    Subgroup (K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup) :=
  (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K).range

end
end Langlands.NYLL.ClassFormation
