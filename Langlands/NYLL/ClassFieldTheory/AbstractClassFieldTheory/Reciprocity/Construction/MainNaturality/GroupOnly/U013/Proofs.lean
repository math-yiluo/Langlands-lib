/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.GroupOnly.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs

/-!
# NYLL M066.013: finiteness of the composite quotient in the naturality tower

Modified by Worker 735, 16 November 2026: extract the source-private theorem
`finiteReciprocityNaturality_tower_finite` (M066.013) from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as the public port-internal
theorem `Langlands.NYLL.PortInternal.M066.d013`; prefix the namespace with
`Langlands.NYLL`, import the published statement module and the published
proof of `relativeTowerQuotientFinite` (M026.014) instead of the source
import, state the theorem through the published
`Langlands.NYLL.PortInternal.M066.d013Statement`, whose finiteness binders and
conclusion write the source's `extensionSubgroup` quotients through their
`Subgroup.subgroupOf` bodies, and omit the source `private` modifier. The
source proof term `relativeTowerQuotientFinite K K' L' hL'K' hK'K` is retained
unchanged. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Finiteness of the upper-left-to-lower-right composite extension in the
first diagram. This is the private source theorem
`ClassFormation.finiteReciprocityNaturality_tower_finite`. -/
theorem _root_.Langlands.NYLL.PortInternal.M066.d013
    (K K' L' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    [Finite (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup)]
    [Finite (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup)] :
    Langlands.NYLL.PortInternal.M066.d013Statement K K' L' hK'K hL'K' :=
  relativeTowerQuotientFinite K K' L' hL'K' hK'K

end
end Langlands.NYLL.ClassFormation
