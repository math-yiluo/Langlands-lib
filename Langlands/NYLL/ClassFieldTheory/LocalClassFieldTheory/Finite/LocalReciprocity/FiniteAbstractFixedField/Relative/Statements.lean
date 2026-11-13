/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Definitions

/-!
# Relative fixing subgroup image and normality targets

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory
noncomputable section
def map_extensionSubgroup_abstractSubgroupEquivStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) : Prop :=
(L.toSubgroup.subgroupOf K.toSubgroup).map
        (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom =
      (abstractRelativeFixedField k Ω hLK).fixingSubgroup

def abstractRelativeFixingSubgroup_normalStatement
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) : Prop :=
(abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal

end
end Langlands.NYLL.LocalClassFieldTheory
