/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions

/-!
# Concrete abstract fixed fields and their absolute Galois groups

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory
noncomputable section
variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
/-- The concrete fixed field represented by an abstract closed subgroup. -/
abbrev abstractFixedField (H : ClosedSubgroup (Gal(Ω/k))) :
    IntermediateField k Ω :=
  IntermediateField.fixedField H.toSubgroup

/-- The abstract subgroup representing a fixed field is canonically the
absolute Galois group of the ambient extension over that fixed field. -/
def abstractSubgroupEquivGaloisGroup
    (H : ClosedSubgroup (Gal(Ω/k))) :
    H.toSubgroup ≃* Gal(Ω/abstractFixedField k Ω H) :=
  (MulEquiv.subgroupCongr
      (InfiniteGalois.fixingSubgroup_fixedField H).symm).trans
    (IntermediateField.fixingSubgroupEquiv (abstractFixedField k Ω H))
end
end Langlands.NYLL.LocalClassFieldTheory
