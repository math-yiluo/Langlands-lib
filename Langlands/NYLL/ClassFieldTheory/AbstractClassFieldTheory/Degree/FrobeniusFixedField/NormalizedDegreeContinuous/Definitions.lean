/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.U002.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U010.Proofs

/-!
# The continuous factorized normalized degree and its kernel restriction

Modified by Worker 5264: extract M014.016 `extensionNormalizedDegreeContinuous`
and M014.020 `extensionDegreeKernelRestriction` from the pinned NYLL
FrobeniusFixedField source with the Langlands.NYLL namespace prefix. The
source-private helper M014.002 `continuousQuotientLift` is the published
`Langlands.NYLL.PortInternal.M014.d002`. In the kernel-containment proof inside
M014.016, the source rewrite with the theorem M011.010 `normalizedDegree_ker`
uses that published theorem through a local equation. As in the published
sibling modules, `extensionSubgroup K.field L hLK` is expanded to its exact
Mathlib body `L.toSubgroup.subgroupOf K.field.toSubgroup`. The source imports
are replaced by focused published imports. The source universe and variable
declarations, docstrings, binders and remaining construction bodies are
retained. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The factorized normalized degree as a continuous homomorphism. -/
def extensionNormalizedDegreeContinuous (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) →ₜ* ZHatMul :=
  { toMonoidHom := D.extensionNormalizedDegree K L hLK
    continuous_toFun :=
      (Langlands.NYLL.PortInternal.M014.d002 (D.extensionInertiaWithin K.field L hLK)
        (D.normalizedDegree K)
        (by
          intro x hx
          have hker :
              (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field :=
            D.normalizedDegree_ker K
          rw [hker]
          exact hx.2)).continuous_toFun }

/-- Restriction embeds the kernel of `d_K` on `G(\widetilde L|K)` into
the finite group `G(L|K)`. -/
def extensionDegreeKernelRestriction (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker →*
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) :=
  (D.extensionRestriction K.field L hLK).comp
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker.subtype

end DegreeData

end
end Langlands.NYLL.ClassFormation
