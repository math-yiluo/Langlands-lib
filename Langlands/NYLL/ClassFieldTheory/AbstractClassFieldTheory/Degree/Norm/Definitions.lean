/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Action.Basic
import Mathlib.GroupTheory.Index
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions

/-!
# Relative coset action and norm-value data

Modified by Worker 200, 13 November 2026: extract M024.001, .003 and .005
from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published fixed-subgroup data, and replace
`extensionSubgroup K L hLK` by its exact Mathlib `Subgroup.subgroupOf` body.
Keep the source constructions and embedded proof terms.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

open scoped BigOperators

-- Mathlib's `Rep ℤ G` currently fixes `G` to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The value of a fixed coefficient at a left coset.  This is independent
of the representative precisely because the coefficient is fixed by the
smaller abstract-field subgroup. -/
def relativeCosetAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) : A.V :=
  Quotient.liftOn' q (fun k : K.toSubgroup => A.ρ k.1 a.1) (by
    intro x y hxy
    have hmem : x⁻¹ * y ∈ (L.toSubgroup.subgroupOf K.toSubgroup) :=
      QuotientGroup.leftRel_apply.mp hxy
    let l : L.toSubgroup := ⟨(x⁻¹ * y).1, hmem⟩
    have hy : y = x * ⟨l.1, hLK l.2⟩ := by
      apply Subtype.ext
      simp [l]
    rw [hy]
    change A.ρ x.1 a.1 = A.ρ (x.1 * l.1) a.1
    rw [map_mul]
    change A.ρ x.1 a.1 = A.ρ x.1 (A.ρ l.1 a.1)
    rw [a.2 l])

/-- Left multiplication permutes the cosets of an arbitrary subgroup. -/
def leftMulCosetEquiv {G : Type*} [Group G]
    (H : Subgroup G) (g : G) : (G ⧸ H) ≃ (G ⧸ H) :=
  MulAction.toPerm g

/-- The additive norm value from `A_L` to the ambient module. -/
def relativeNormValue
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A L) : A.V := by
  letI := Fintype.ofFinite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
  exact ∑ q, relativeCosetAction A K L hLK a q

end
end Langlands.NYLL.ClassFormation
