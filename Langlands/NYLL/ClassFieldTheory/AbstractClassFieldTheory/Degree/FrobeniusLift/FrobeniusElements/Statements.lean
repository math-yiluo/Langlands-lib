/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Definitions

/-!
# Targets for the factorized normalized degree and Frobenius lifting

Modified by Worker 5264: extract the public theorem signatures M012.006
`extensionNormalizedDegree_mk` and M012.013 `frobeniusRestriction_surjective`
from the pinned NYLL FrobeniusLift source as Prop-valued Statement
definitions. Prefix the namespace with Langlands.NYLL, append `Statement` to
each name, expand `extensionSubgroup K.field L hLK` to its exact Mathlib body
`L.toSubgroup.subgroupOf K.field.toSubgroup`, keep the source universe and
variable declarations, parameters and binder kinds, and omit the proofs.
The instance binder `hLfinite` is used only by the source proof, so the
unused-variable linter is silenced for M012.013's statement.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: the identity `D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) =
D.normalizedDegree K k`. -/
def extensionNormalizedDegree_mkStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (k : K.field.toSubgroup) : Prop :=
  D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) =
    D.normalizedDegree K k

set_option linter.unusedVariables false in
/-- Target, **the finite degree-quotient decomposition**: for a finite Galois
extension `L | K`, restriction maps the Frobenius semigroup onto `G(L|K)`. -/
def frobeniusRestriction_surjectiveStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    Prop :=
  Function.Surjective (D.frobeniusRestriction K L hLK)

end DegreeData

end
end Langlands.NYLL.ClassFormation
