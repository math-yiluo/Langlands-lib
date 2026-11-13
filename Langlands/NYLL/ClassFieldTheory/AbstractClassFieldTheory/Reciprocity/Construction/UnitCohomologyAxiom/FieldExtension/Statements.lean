/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom.FieldExtension.Definitions

/-!
# NYLL M032.011: unramifiedness of the finite field-extension bundle

Modified by Worker 5424: extract the signature of M032.011 from the pinned
NYLL UnitCohomologyAxiom.lean, prefix its namespace with Langlands.NYLL, and
replace the theorem with a Prop-valued Statement definition with the same
telescope and conclusion. Use the focused import of the M032 field-extension
module. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace FiniteUnramifiedCyclicExtension

variable {K : FiniteAbstractField G}

/-- Target: the unramified proof transported to the canonical finite
field-extension bundle. -/
def toFiniteAbstractFieldExtension_isUnramifiedStatement
    (E : FiniteUnramifiedCyclicExtension D K) : Prop :=
  E.toFiniteAbstractFieldExtension.IsUnramified D

end FiniteUnramifiedCyclicExtension

end
end Langlands.NYLL.ClassFormation
