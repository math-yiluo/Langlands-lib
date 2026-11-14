/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs

/-!
# NYLL M034.004: finite intermediate fields of a finite field are finite

Modified by Worker 483: extract the signature of M034.004 from the pinned
NYLL FiniteIntermediateCompositum.lean, prefix its namespace with
Langlands.NYLL, and replace the theorem with a Prop-valued Statement
definition. Preserve the `Type*` universe, the full telescope, binder kinds
and order and every hypothesis; underscore the unused finiteness instance
name. Use focused published imports. See the paired Markdown and
licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- Target: a finite intermediate field over a finite abstract base field is
itself finite over the global base field. -/
def absoluteFiniteStatement {E K : ClosedSubgroup G}
    [_hKfinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K (le_baseField K))]
    (M : FiniteIntermediateField E K) : Prop :=
  Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) M.field (le_baseField M.field))

end FiniteIntermediateField

end
end Langlands.NYLL.ClassFormation
