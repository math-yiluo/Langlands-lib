/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions

/-!
# Relative coset action and norm-value statement targets

Modified by Worker 200, 13 November 2026: extract the statements of
M024.002, .004, .006 and .008 from the pinned NYLL `Degree/Norm.lean`;
prefix the namespace with `Langlands.NYLL`, use the published data,
replace `extensionSubgroup` by its exact `Subgroup.subgroupOf` body, and
publish Prop-valued definitions with the `Statement` suffix.
The source theorem proofs and simp attributes are omitted.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Target: the relative coset action on a quotient representative is the
corresponding group action. -/
def relativeCosetAction_mkStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A L) (k : K.toSubgroup) : Prop :=
    relativeCosetAction A K L hLK a (QuotientGroup.mk k) = A.ρ k.1 a.1

/-- Target: left multiplication sends the coset of `x` to that of `g * x`. -/
def leftMulCosetEquiv_mkStatement {G : Type*} [Group G]
    (H : Subgroup G) (g x : G) : Prop :=
    leftMulCosetEquiv H g (QuotientGroup.mk x) = QuotientGroup.mk (g * x)

/-- Target: the relative coset action is additive in the represented fixed
element. -/
def relativeCosetAction_addStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a b : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) : Prop :=
    relativeCosetAction A K L hLK (a + b) q =
      relativeCosetAction A K L hLK a q +
        relativeCosetAction A K L hLK b q

/-- Target: the relative norm value is fixed by the base subgroup action. -/
def relativeNormValue_fixedStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A L) (k : K.toSubgroup) : Prop :=
    A.ρ k.1 (relativeNormValue A K L hLK a) =
      relativeNormValue A K L hLK a

end
end Langlands.NYLL.ClassFormation
