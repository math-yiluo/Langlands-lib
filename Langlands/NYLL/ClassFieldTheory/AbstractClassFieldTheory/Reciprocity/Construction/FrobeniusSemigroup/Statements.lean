/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup.Definitions

/-!
# Target about the Frobenius semigroup

Modified by Worker 5264, 15 November 2026: state the source theorem M015.003
`frobeniusMul_coe` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement` to
the name, expand `CyclicCohomology.extensionSubgroup (G := G) K.field L hLK`
to its exact Mathlib body `L.toSubgroup.subgroupOf K.field.toSubgroup`, keep
the source variable declaration, parameters and binder kinds, and omit the
proof and the `@[simp]` attribute. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

namespace DegreeData

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Target: the identity `(σ * τ).1 = σ.1 * τ.1`. -/
def frobeniusMul_coeStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK) : Prop :=
    (σ * τ).1 = σ.1 * τ.1

end DegreeData

end
end Langlands.NYLL.ClassFormation
