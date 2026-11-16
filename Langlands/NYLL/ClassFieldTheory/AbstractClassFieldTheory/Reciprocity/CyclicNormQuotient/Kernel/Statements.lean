/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.CyclicNormQuotient.NormClass.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions

/-!
# NYLL cyclic norm-class kernel target

Modified by Worker 196, 16 November 2026: extract the exact type of M074.005,
source CyclicNormQuotient.lean:203–219 at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, append `Statement`, and define the theorem type as a proposition.
Omit the proof, expand `extensionSubgroup` to its Mathlib body, and replace the
generator-cyclicity helper with its Mathlib equivalent. Retain the entire source
telescope and five local instances. Import the published norm-class map and norm
subgroup. See the paired Markdown and `licenses/NYLL/`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory CyclicCohomology CategoryTheory
noncomputable section
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The concrete Tate-class kernel is the actual relative-norm image. -/
def cyclicNormClassHom_kerStatement
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup))
    (g : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
    let _ : (L.toSubgroup.subgroupOf K.toSubgroup).Normal := hnormal
    let _ : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) := hfinite
    let _ : Fintype (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      Fintype.ofFinite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    let _ : IsCyclic (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      isCyclic_iff_exists_zpowers_eq_top.mpr
        ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩
    let _ : CommGroup (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      IsCyclic.commGroup
    (cyclicNormClassHom A K L hLK hnormal hfinite g hg).ker =
      finiteNormSubgroup A K L hLK

end
end Langlands.NYLL.ClassFormation
