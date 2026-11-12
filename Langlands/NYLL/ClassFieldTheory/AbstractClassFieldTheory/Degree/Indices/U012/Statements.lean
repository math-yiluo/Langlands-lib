/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U010.Definitions
import Mathlib.GroupTheory.Index

/-!
# Targets for cardinal-valued relative-index laws

Modified by Worker 120: extract the signatures of M006.012–014 from
the pinned NYLL Degree/Indices.lean, prefix the namespace by Langlands.NYLL,
and replace the source theorems by Prop-valued Statement definitions.
Reuse the published M006.010–011 data and a focused Mathlib import.
Preserve the source universe, argument order and hypotheses; omit unused
section parameters D and Group D and the theorem-only simp attribute.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G]

/-- Target for comparison with natural relative index at a finite coset boundary. -/
def relativeIndexCardinal_eq_index_of_finiteStatement
    {L K : Subgroup G} (hLK : L ≤ K) [Finite (K ⧸ L.subgroupOf K)] : Prop :=
  relativeIndexCardinal hLK = (L.relIndex K : Cardinal)

/-- Target for the cardinal index of a subgroup in itself. -/
def relativeIndexCardinal_selfStatement (K : Subgroup G) : Prop :=
  relativeIndexCardinal (le_refl K) = 1

/-- Target for multiplication of cardinal relative indices in an arbitrary tower. -/
def relativeIndexCardinal_mulStatement {M L K : Subgroup G}
    (hML : M ≤ L) (hLK : L ≤ K) : Prop :=
  relativeIndexCardinal hML * relativeIndexCardinal hLK =
    relativeIndexCardinal (hML.trans hLK)

end Langlands.NYLL.ClassFormation
