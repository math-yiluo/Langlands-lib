/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.Cohomology.Continuous.FiniteQuotientSystem

/-!
# Continuous subgroup inclusion

Modified by Worker 193: extract M014.003 from the pinned NYLL source,
give its private helper the prescribed public internal name, and reuse
Langlands.Continuous.subgroupInclusion through its defining module. Retain the
source parameter telescope; the delegated construction is definitionally equal
to the source body. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.PortInternal.M014

noncomputable section

/-- Inclusion of a subgroup with its subtype topology, used locally below. -/
def d003
    {A : Type*} [Group A] [TopologicalSpace A]
    (H : Subgroup A) : H →ₜ* A :=
  Langlands.Continuous.subgroupInclusion H

end
end Langlands.NYLL.PortInternal.M014
