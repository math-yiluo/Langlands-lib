/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions

/-!
# Target for membership in the ambient fixed additive subgroup

Modified by Worker 5454: extract the asserted type of M023.002
`KummerTheory.mem_ambientFixedAddSubgroup_iff` from the pinned NYLL
`Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean` (section variables
line 30, theorem lines 46–53) as a Prop-valued definition. Prefix the
namespace with `Langlands.NYLL`, append `Statement` to the theorem name, keep
the section variables of line 30 in the same order and binder kinds followed
by the theorem's own parameters, and omit the proof `Iff.rfl` and the
`@[simp]` attribute. The source's module imports and its unused
`open CyclicCohomology` are replaced by the published M023.001 module, which
supplies `ambientFixedAddSubgroup`. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Membership in the ambient fixed subgroup is equivalent to invariance under every
subgroup element. -/
def mem_ambientFixedAddSubgroup_iffStatement
    (A : Rep ℤ G) (H : ClosedSubgroup G) (a : A.V) : Prop :=
  a ∈ ambientFixedAddSubgroup A H ↔
    ∀ h : H.toSubgroup, A.ρ h.1 a = a

end

end Langlands.NYLL.KummerTheory
