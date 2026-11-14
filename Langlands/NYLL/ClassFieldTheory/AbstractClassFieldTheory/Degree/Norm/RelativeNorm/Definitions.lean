/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.U008.Proofs

/-!
# The relative norm homomorphism

Modified by Worker 96, 14 November 2026: extract M024.009 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published proofs of M024.006 and M024.008,
replace `extensionSubgroup K L hLK` by its exact `Subgroup.subgroupOf` body,
and, in the embedded `map_zero'` proof, prove the zero coset-action fact
(the source simp lemma M024.007) inline before the source `simp` call.
The homomorphism, its `toFun` and the `map_add'` proof are unchanged.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

open scoped BigOperators

-- Mathlib's `Rep ℤ G` currently fixes `G` to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The norm homomorphism for a finite abstract extension `L | K`.

In the multiplicative notation of the construction this additive sum is the product
over a system of representatives of `G_K / G_L`.  Its codomain is the
actual fixed module `A_K`, with fixedness proved by coset reindexing. -/
def relativeNorm
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] :
    ambientFixedAddSubgroup A L →+ ambientFixedAddSubgroup A K where
  toFun a := ⟨relativeNormValue A K L hLK a,
    relativeNormValue_fixed A K L hLK a⟩
  map_zero' := by
    apply Subtype.ext
    let := Fintype.ofFinite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
    have hzero : ∀ q : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup),
        relativeCosetAction A K L hLK 0 q = 0 := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro k
      change A.ρ k.1 (0 : ambientFixedAddSubgroup A L).1 = 0
      exact map_zero (A.ρ k.1)
    simp [relativeNormValue, hzero]
  map_add' a b := by
    apply Subtype.ext
    let := Fintype.ofFinite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
    simp only [AddSubgroup.coe_add, relativeNormValue]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    exact relativeCosetAction_add A K L hLK a b q

end
end Langlands.NYLL.ClassFormation
