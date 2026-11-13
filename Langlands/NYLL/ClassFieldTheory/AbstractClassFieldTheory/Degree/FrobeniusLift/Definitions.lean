/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions

/-!
# NYLL relative extension inertia and restriction

Modified by Worker 191: extract M012.002, .003 and .007 from the pinned
FrobeniusLift source; prefix the namespace with Langlands.NYLL and expand
extensionSubgroup to its exact Mathlib Subgroup.subgroupOf body. Preserve
the source binders, construction bodies and normality proof. Replace the
full Frobenius import by the published focused degree-data import.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- `I_L`, viewed inside `G_K`; this is `G_{\widetilde L}`. -/
def extensionInertiaWithin (D : DegreeData G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) : Subgroup K.toSubgroup :=
  L.toSubgroup.subgroupOf K.toSubgroup ⊓ D.fieldInertiaWithin K

/--
The relative inertia subgroup is normal whenever the full extension subgroup is normal.
-/
instance extensionInertiaWithin_normal (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (D.extensionInertiaWithin K L hLK).Normal := by
  rw [extensionInertiaWithin]
  infer_instance

/-- Restriction from `G(\widetilde L|K)` to `G(L|K)`. -/
def extensionRestriction (D : DegreeData G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) →*
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
  QuotientGroup.map (D.extensionInertiaWithin K L hLK)
    (L.toSubgroup.subgroupOf K.toSubgroup) (MonoidHom.id K.toSubgroup) inf_le_left

end DegreeData

end
end Langlands.NYLL.ClassFormation
