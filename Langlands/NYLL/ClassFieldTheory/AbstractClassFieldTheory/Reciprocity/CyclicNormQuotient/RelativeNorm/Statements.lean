/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.FixedCycle.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions

/-!
# NYLL cyclic fixed-cycle relative norm target

Modified by Worker 196, 14 November 2026: extract the exact theorem type of
M074.004, CyclicNormQuotient.lean:172–193 at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, append `Statement`, and make the theorem type the body of
a Prop-valued definition. Omit the proof, use focused published imports,
expand `extensionSubgroup` to its Mathlib body, and use the equivalent
Mathlib generator-cyclicity proof. Keep the full telescope and local instances.
See the paired Markdown and `licenses/NYLL/`.
-/

namespace Langlands.NYLL.ClassFormation
open KummerTheory CyclicCohomology CategoryTheory
noncomputable section
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Under the fixed-cycle equivalence, the actual relative norm is the
first differential in the cyclic Tate complex. -/
def cyclicFixedCycleEquiv_relativeNormStatement
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : ((L.toSubgroup.subgroupOf K.toSubgroup)).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)))
    (g : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (a : ambientFixedAddSubgroup A L) : Prop :=
    let _ : ((L.toSubgroup.subgroupOf K.toSubgroup)).Normal := hnormal
    let _ : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) := hfinite
    let _ : Fintype (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) :=
      Fintype.ofFinite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
    let _ : IsCyclic (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) :=
      isCyclic_iff_exists_zpowers_eq_top.mpr
        ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩
    let _ : CommGroup (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg
        (relativeNorm A K L hLK a) =
      T.moduleCatToCycles
        ((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a)

end
end Langlands.NYLL.ClassFormation
