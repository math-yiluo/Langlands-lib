/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.FixedCarrier.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions

/-!
# NYLL extension fixed representation action target

Modified by Worker 196, 13 November 2026: extract M073.004 (FieldRepresentation.lean:87–95) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with `Langlands.NYLL`, use focused
imports and expand the extension-subgroup abbreviation to its exact Mathlib body.
See the paired Markdown for the full correspondence and all modifications, and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory CyclicCohomology

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The quotient action on `A_L` is the same coset action used by the
relative norm. -/
def extensionFixedRepresentation_action_coeStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : ((L.toSubgroup.subgroupOf K.toSubgroup)).Normal)
    (q : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) : Prop :=
    ((extensionFixedRepresentation A K L hLK hnormal).ρ q a).1 =
      relativeCosetAction A K L hLK
        (extensionFixedRepresentationEquiv A K L hLK hnormal a) q

end
end Langlands.NYLL.ClassFormation
