/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Main.Definitions

/-!
# NYLL M029: targets for the infinite and maximal-unramified norm subgroups

Modified by Worker 171, 14 November 2026: extract the signatures of the
source theorems M029.005, M029.011, M029.015, M029.025, M029.026 and M029.032
from the pinned NYLL NormSubgroup.lean at
fbd320cd8b1b06487c58227e92eb135794267709, prefix their namespace with
Langlands.NYLL, and replace each theorem by a Prop-valued Statement
definition whose body is the source statement. Preserve the full telescopes,
binder kinds and order and every hypothesis. Omit the proofs and the simp
attributes, the other declarations of the source file and the unused
`universe u`. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

section infiniteNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Target for M029.005.  Membership in the infinite norm subgroup is
characterized by norms from every finite level. -/
def mem_infiniteNormSubgroup_iffStatement
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) : Prop :=
  a ∈ infiniteNormSubgroup A E K ↔
    ∀ M : FiniteIntermediateField E K,
      a ∈ finiteIntermediateNormRange A E K M

/-- Target for M029.011.  An infinite norm class vanishes exactly when its
representative lies in the norm subgroup. -/
def infiniteNormClass_eq_zero_iffStatement
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) : Prop :=
  infiniteNormClass A E K a = 0 ↔
    a ∈ infiniteNormSubgroup A E K

/-- Target for M029.015.  Lifting the canonical infinite norm class recovers
its representative in the concrete quotient. -/
def infiniteNormQuotientLift_infiniteNormClassStatement
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : infiniteNormSubgroup A E K ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) : Prop :=
  infiniteNormQuotientLift A E K f hf (infiniteNormClass A E K a) = f a

end infiniteNorms

section maximalUnramifiedNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target for M029.025.  The maximal-unramified norm subgroup is the
infinite norm subgroup for the maximal unramified field. -/
def maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroupStatement
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) : Prop :=
  D.maximalUnramifiedNormSubgroup A K L =
    infiniteNormSubgroup A (D.maximalUnramifiedField L) K

/-- Target for M029.026.  Membership in the maximal unramified norm subgroup
is characterized levelwise. -/
def mem_maximalUnramifiedNormSubgroup_iffStatement
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) : Prop :=
  a ∈ D.maximalUnramifiedNormSubgroup A K L ↔
    a ∈ infiniteNormSubgroup A (D.maximalUnramifiedField L) K

/-- Target for M029.032.  A maximal-unramified norm class vanishes exactly on
its defining norm subgroup. -/
def maximalUnramifiedNormClass_eq_zero_iffStatement
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) : Prop :=
  D.maximalUnramifiedNormClass A K L a = 0 ↔
    a ∈ D.maximalUnramifiedNormSubgroup A K L

end DegreeData

end maximalUnramifiedNorms

end
end Langlands.NYLL.ClassFormation
