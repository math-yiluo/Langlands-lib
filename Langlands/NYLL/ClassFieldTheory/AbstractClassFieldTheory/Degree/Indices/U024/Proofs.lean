/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U023.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U006.Definitions

/-!
# Cardinal kernel index and saturation

Modified by Worker 185: extract NYLL M006.024, prefix the namespace with
Langlands.NYLL, and state the theorem using its published Statement target.
Reuse the published kernel coset equivalence and retain the source proof.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

universe u v

variable {G : Type u} {D : Type v} [Group G] [Group D]

/-- Cardinal form of the kernel contribution: intersecting both subgroups
with the kernel gives the saturated inner index. -/
theorem relativeIndexCardinal_kernel_eq_saturation (d : G →* D)
    {L K : Subgroup G} (hLK : L ≤ K) :
    relativeIndexCardinal_kernel_eq_saturationStatement d hLK := by
  exact Cardinal.mk_congr (kernelCosetEquivSaturation d hLK)

end Langlands.NYLL.ClassFormation
