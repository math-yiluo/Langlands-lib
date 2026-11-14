/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.FixedCarrier.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions

/-!
# NYLL extension fixed representation norm comparison target

Modified by Worker 196, 14 November 2026: extract the theorem type of M073.005,
FieldRepresentation.lean:104–116 at fbd320cd8b1b06487c58227e92eb135794267709.
Prefix the namespace with `Langlands.NYLL`, append `Statement`, and put the
source theorem type in a Prop-valued definition. Omit the proof, use focused
published imports, and expand `extensionSubgroup` to its exact Mathlib body.
Every source binder and local instance is retained. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation
open KummerTheory CyclicCohomology
noncomputable section
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The norm in the descended representation is the actual relative norm
on the underlying fixed coefficient. -/
def extensionFixedRepresentation_norm_coeStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : ((L.toSubgroup.subgroupOf K.toSubgroup)).Normal)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) : Prop :=
    letI := hnormal
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
    ((extensionFixedRepresentation A K L hLK hnormal).norm.hom a).1 =
      ((relativeNorm A K L hLK
        (extensionFixedRepresentationEquiv A K L hLK hnormal a) :
          ambientFixedAddSubgroup A K) : A.V)

end
end Langlands.NYLL.ClassFormation
