/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.FixedCycle.Definitions

/-!
# NYLL cyclic norm-class homomorphism

Modified by Worker 196, 13 November 2026: extract M074.002, lines 117–140,
from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace with
`Langlands.NYLL`, use the focused fixed-cycle import, expand `extensionSubgroup`
to its Mathlib definition, and replace the generator-cyclicity helper by its
Mathlib equivalent. Retain the full source telescope, local instances, and
construction. See the paired Markdown and `licenses/NYLL/`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory CyclicCohomology CategoryTheory
noncomputable section
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The canonical map from `A_K` to the concrete kernel/range quotient
computing degree-zero Tate cohomology. -/
def cyclicNormClassHom
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup))
    (g : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    let _ : (L.toSubgroup.subgroupOf K.toSubgroup).Normal := hnormal
    let _ : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) := hfinite
    let _ : Fintype (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      Fintype.ofFinite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    let _ : IsCyclic (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      isCyclic_iff_exists_zpowers_eq_top.mpr
        ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩
    let _ : CommGroup (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    ambientFixedAddSubgroup A K →+
      T.moduleCatLeftHomologyData.H := by
  intro instNormal instFinite instFintype instCyclic instCommGroup M T
  let e := cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg
  exact T.moduleCatLeftHomologyData.π.hom.toAddMonoidHom.comp e.toAddMonoidHom

end
end Langlands.NYLL.ClassFormation
