/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 9, 13 November 2026 UTC:
Extract only the proof of M068.003 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainTransferFrobeniusGeometry.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published
MainTransferFrobeniusGeometry.GroupOnly.Statements module. State the
theorem as the published Statement applied to the source parameters.
Replace each occurrence of the source abbreviation extensionSubgroup X Y h
by its Mathlib body Y.toSubgroup.subgroupOf X.toSubgroup, and the two
rewrites by KummerTheory.mem_extensionSubgroup_iff (whose source proof is
Iff.rfl) by rewrites with Mathlib's Subgroup.mem_subgroupOf. Unfold the
Statement in the rewrite before hcomap. The proof is otherwise the
original one line for line. Keep the source universe u and section
variables {G : Type u} [Group G] [TopologicalSpace G]. The original
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobeniusGeometry.GroupOnly.Statements

/-!
# Normality of `L` in an intermediate field

The exact proof that if `L` is normal in `K` then `L` is normal in every
intermediate `K'` with `L ≤ K' ≤ K`.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Normality of `L | K` restricts to every intermediate field `K'`. -/
theorem transferNormNaturality_intermediateExtension_normal
    (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    transferNormNaturality_intermediateExtension_normalStatement K K' L hLK' hK'K := by
  have hcomap : L.toSubgroup.subgroupOf K'.toSubgroup =
      (L.toSubgroup.subgroupOf K.toSubgroup).comap
        (Subgroup.inclusion hK'K) := by
    ext k'
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  rw [transferNormNaturality_intermediateExtension_normalStatement, hcomap]
  exact hLnormal.comap (Subgroup.inclusion hK'K)

end Langlands.NYLL.ClassFormation
