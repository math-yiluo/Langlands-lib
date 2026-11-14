/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs

/-!
# Conjugate closed subgroup, absolute extension, normal-extension action and
tower finiteness statement targets

Modified by Worker 165, 14 November 2026: extract the statements of M026.002,
.006, .012 and .014 from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, name the private source theorem's target
`Langlands.NYLL.PortInternal.M026.d006Statement`, use the published data, and
publish Prop-valued definitions with the `Statement` suffix. The source theorem
proofs and simp attributes are omitted. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators Pointwise

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Target: `x ∈ conjugateClosedSubgroup K σ` exactly when `σ * x * σ⁻¹ ∈ K`. -/
def conjugateClosedSubgroup_memStatement {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G]
    (K : ClosedSubgroup G) (σ x : G) : Prop :=
    x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K

/-- Target for the private source theorem `ClassFormation.mem_absoluteExtension`:
an element of the absolute subgroup lies in the relative subgroup of `K` over
the base field exactly when its underlying element lies in `K`. -/
def _root_.Langlands.NYLL.PortInternal.M026.d006Statement {G : Type*} [Group G]
    [TopologicalSpace G]
    (K : ClosedSubgroup G)
    (x : (baseField G).toSubgroup) : Prop :=
    x ∈ extensionSubgroup (baseField G) K
        (le_baseField K) ↔ x.1 ∈ K

/-- Target: the underlying ambient element of the normal-extension action of
`k` on `a` is `A.ρ k.1 a.1`. -/
def normalExtensionAction_coeStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) : Prop :=
    ((normalExtensionAction A K L hLK hnormal k a : ambientFixedAddSubgroup A L) : A.V) =
      A.ρ k.1 a.1

/-- Target: finiteness of relative coset spaces is closed under composition in
a tower of closed subgroups. -/
def relativeTowerQuotientFiniteStatement
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [Finite (L.toSubgroup ⧸ extensionSubgroup L M hML)] : Prop :=
    Finite
      (K.toSubgroup ⧸ extensionSubgroup K M (hML.trans hLK))

end
end Langlands.NYLL.ClassFormation
