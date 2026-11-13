/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 172, 13 November 2026 UTC:
Extract only the proof of M006.012 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published U012 Statements module.
State the theorem as the published Statement applied to the source
parameters, and unfold that Statement before the original rewrites and
the original Nat.cast_card.symm step. Preserve universe u, implicit G,
Group G, implicit L and K, explicit hLK and the finite coset-type instance.
Omit the unused source section variables D, Group D and universe v.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U012.Statements

/-!
# Cardinal relative index at a finite coset boundary

The exact proof that the cardinal-valued relative index of `L ≤ K` equals
Mathlib's natural relative index, cast to a cardinal, when the relative coset
type `K ⧸ L.subgroupOf K` is finite.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G]

/-- At an explicitly finite boundary, the cardinal relative index specializes
to Mathlib's natural-valued relative index. -/
theorem relativeIndexCardinal_eq_index_of_finite {L K : Subgroup G} (hLK : L ≤ K)
    [Finite (K ⧸ L.subgroupOf K)] :
    relativeIndexCardinal_eq_index_of_finiteStatement hLK := by
  rw [relativeIndexCardinal_eq_index_of_finiteStatement, relativeIndexCardinal,
    intersectionIndexCardinal, Subgroup.relIndex, Subgroup.index]
  exact Nat.cast_card.symm

end Langlands.NYLL.ClassFormation
