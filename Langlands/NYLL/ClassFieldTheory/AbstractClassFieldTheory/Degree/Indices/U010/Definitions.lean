/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 11 November 2026:
Extract M006.010–011 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL and replace the source import by the required Mathlib
imports. Preserve the definitions, docstrings, universe and parameters.
Unused source section variables D and Group D are omitted.
The upstream LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cardinal indices of subgroup inclusions

The actual cardinality of relative cosets, including infinite coset spaces.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G]

/-- The cardinality of the coset type of the intersection of two subgroups.

This is defined for arbitrary subgroups.  For the cardinal relative index of
an inclusion, use `relativeIndexCardinal`, which records the inclusion in its
domain. -/
noncomputable def intersectionIndexCardinal (L K : Subgroup G) : Cardinal :=
  Cardinal.mk (K ⧸ L.subgroupOf K)

/-- The cardinality of the actual relative coset type of a subgroup inclusion. -/
noncomputable def relativeIndexCardinal {L K : Subgroup G} (_ : L ≤ K) : Cardinal :=
  intersectionIndexCardinal L K

end Langlands.NYLL.ClassFormation
