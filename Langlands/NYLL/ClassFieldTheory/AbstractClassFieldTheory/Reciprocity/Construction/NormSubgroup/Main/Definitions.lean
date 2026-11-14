/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions

/-!
# NYLL M029: the infinite and maximal-unramified norm quotients

Modified by Worker 171, 14 November 2026: extract M029.006, M029.007,
M029.009, M029.014, M029.027, M029.028 and M029.030 from the pinned NYLL
NormSubgroup.lean at fbd320cd8b1b06487c58227e92eb135794267709, prefix the
namespace with Langlands.NYLL and replace the source imports by the focused
published import of the infinite norm subgroups. Omit every other declaration
of the source file and the unused `universe u`. The declarations, binders,
docstrings, instance scopes and tactic bodies are otherwise unchanged. See the
paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

section infiniteNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The quotient `A_K / N_{E|K} A_E` used by the reciprocity map.

This public object is opaque: clients use `infiniteNormClass`,
`InfiniteNormQuotient.induction_on`, or `infiniteNormQuotientLift` instead of
depending on the concrete quotient representation. -/
def InfiniteNormQuotient
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :=
  ambientFixedAddSubgroup A K ⧸ infiniteNormSubgroup A E K

/-- The additive group structure on the infinite norm quotient. -/
instance infiniteNormQuotientAddCommGroup
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    AddCommGroup (InfiniteNormQuotient A E K) := by
  unfold InfiniteNormQuotient
  infer_instance

/-- The canonical class map into the infinite norm quotient. -/
def infiniteNormClass
    (A : Rep ℤ G) (E K : ClosedSubgroup G) :
    ambientFixedAddSubgroup A K →+
      InfiniteNormQuotient A E K := by
  unfold InfiniteNormQuotient
  exact QuotientAddGroup.mk' (infiniteNormSubgroup A E K)

/-- Descend an additive homomorphism that kills the infinite norm subgroup. -/
def infiniteNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (E K : ClosedSubgroup G)
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : infiniteNormSubgroup A E K ≤ f.ker) :
    InfiniteNormQuotient A E K →+ B := by
  unfold InfiniteNormQuotient
  exact QuotientAddGroup.lift (infiniteNormSubgroup A E K) f hf

end infiniteNorms

section maximalUnramifiedNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- `A_K / N_{\widetilde L|K} A_{\widetilde L}`.

This is an opaque public object, not a reducible alias for the infinite norm
quotient. -/
def MaximalUnramifiedNormQuotient (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) :=
  InfiniteNormQuotient A (D.maximalUnramifiedField L) K

/-- The additive group structure on the maximal-unramified norm quotient. -/
instance maximalUnramifiedNormQuotientAddCommGroup
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    AddCommGroup (D.MaximalUnramifiedNormQuotient A K L) := by
  unfold MaximalUnramifiedNormQuotient
  infer_instance

/-- The canonical class map into the maximal-unramified norm quotient. -/
def maximalUnramifiedNormClass
    (D : DegreeData G) (A : Rep ℤ G) (K L : ClosedSubgroup G) :
    ambientFixedAddSubgroup A K →+
      D.MaximalUnramifiedNormQuotient A K L := by
  unfold MaximalUnramifiedNormQuotient
  exact infiniteNormClass A (D.maximalUnramifiedField L) K

end DegreeData

end maximalUnramifiedNorms

end
end Langlands.NYLL.ClassFormation
