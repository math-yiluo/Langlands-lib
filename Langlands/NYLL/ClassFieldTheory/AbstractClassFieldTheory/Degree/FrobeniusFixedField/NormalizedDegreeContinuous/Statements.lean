/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.NormalizedDegreeContinuous.Definitions

/-!
# Targets about the continuous factorized normalized degree

Modified by Worker 5264: state the source theorems M014.017
`extensionNormalizedDegreeContinuous_apply`, M014.019
`extensionNormalizedDegreeContinuous_surjective` and M014.021
`extensionDegreeKernelRestriction_injective` of the pinned NYLL
FrobeniusFixedField source as Prop-valued Statement definitions. Prefix the
namespace with Langlands.NYLL, append `Statement` to each name, expand
`extensionSubgroup K.field L hLK` to `L.toSubgroup.subgroupOf K.field.toSubgroup`,
keep the source universe and variable declarations, parameters and binder
kinds, and omit the proofs and the `@[simp]` attribute.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: the continuous normalized-degree map evaluates as the algebraic
normalized-degree map. -/
def extensionNormalizedDegreeContinuous_applyStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (x : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) : Prop :=
  D.extensionNormalizedDegreeContinuous K L hLK x =
    D.extensionNormalizedDegree K L hLK x

/-- Target: the continuous normalized-degree map of the extension is surjective. -/
def extensionNormalizedDegreeContinuous_surjectiveStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] : Prop :=
  Function.Surjective
    (D.extensionNormalizedDegreeContinuous K L hLK)

/-- Target: restriction to the degree kernel is injective on the extension
subgroup. -/
def extensionDegreeKernelRestriction_injectiveStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] : Prop :=
  Function.Injective
    (D.extensionDegreeKernelRestriction K L hLK)

end DegreeData

end
end Langlands.NYLL.ClassFormation
