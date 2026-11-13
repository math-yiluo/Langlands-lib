/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Extension-subgroup membership target

Modified by Worker 291, 13 November 2026: extract the statement of M022.001
from NYLL's `KummerAbelianAssembly.lean` at
fbd320cd8b1b06487c58227e92eb135794267709, prefix its namespace with
`Langlands.NYLL`, and replace the theorem by a Prop-valued definition with
the `Statement` suffix. Expand `CyclicCohomology.extensionSubgroup` to its
Mathlib `Subgroup.subgroupOf` body as directed by Task 5831. The original
telescope, including the explicit containment proof, is retained.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.KummerTheory

noncomputable section

/-- Target for membership in `G_L` regarded as a subgroup of `G_K`. -/
def mem_extensionSubgroup_iffStatement
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (k : K.toSubgroup) : Prop :=
  k ∈ L.toSubgroup.subgroupOf K.toSubgroup ↔ (k : G) ∈ L

end

end Langlands.NYLL.KummerTheory
