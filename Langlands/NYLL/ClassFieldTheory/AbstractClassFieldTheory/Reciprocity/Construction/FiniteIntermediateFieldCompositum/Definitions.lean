/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions

/-!
# NYLL M037.001: the quotient cardinality of a finite intermediate field

Modified by Worker 483: extract M037.001 from the pinned NYLL
FiniteIntermediateFieldCompositum.lean, prefix the namespace with
Langlands.NYLL and use the focused M029 import. The declaration, its
binders, universe and body are otherwise unchanged. See the paired Markdown
and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

universe u

section finiteIntermediateFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- Cardinality of the finite relative Galois quotient attached to a finite
intermediate field.  Recording the supplied `Finite` instance in the
definition lets later fixed-field constructions use the cardinality without
adding a second finiteness parameter. -/
noncomputable def quotientCard {E K : ClosedSubgroup G}
    (M : FiniteIntermediateField E K) : ℕ := by
  letI : Finite
      (K.toSubgroup ⧸ extensionSubgroup K M.field M.below) := M.finite
  exact Nat.card
    (K.toSubgroup ⧸ extensionSubgroup K M.field M.below)

end FiniteIntermediateField

end finiteIntermediateFields

end
end Langlands.NYLL.ClassFormation
