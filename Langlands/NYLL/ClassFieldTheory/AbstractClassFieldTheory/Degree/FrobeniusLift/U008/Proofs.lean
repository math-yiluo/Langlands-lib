/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5168, 13 November 2026:
Extract the proof of M012.008 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusLift.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, state the theorem as the published proposition
extensionRestriction_mkStatement applied to the source parameters (whose
normality instance binder spells out the source's extensionSubgroup
abbreviation as L.toSubgroup.subgroupOf K.toSubgroup), and omit the
theorem-only simp attribute. The original proof term rfl is unchanged.
Import only the FrobeniusLift Statements module. Omit all other source
declarations. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Statements

/-!
# Extension restriction on quotient representatives

The restriction `G(\widetilde L|K) → G(L|K)` sends the class of `k ∈ G_K`
modulo the relative inertia to the class of `k` modulo `G_L`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/--
Establishes the identity `D.extensionRestriction K L hLK (QuotientGroup.mk k) = QuotientGroup.mk
k`.
-/
theorem extensionRestriction_mk (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) :
    extensionRestriction_mkStatement D K L hLK k :=
  rfl

end DegreeData

end
end Langlands.NYLL.ClassFormation
