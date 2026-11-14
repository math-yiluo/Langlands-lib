/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.CompositumWith.Definitions

/-!
# NYLL M033.009–010: targets for the two compositum bounds

Modified by Worker 483: extract the signatures of M033.009 and M033.010 from
the pinned NYLL ReciprocityIndependence.lean, prefix their namespace with
Langlands.NYLL, and replace each theorem with a Prop-valued Statement
definition. Preserve the universe, the full telescopes, binder kinds and
order. Omit the proofs. See the paired Markdown and licenses/NYLL/LICENSE
and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

section groupTheoreticRefinements

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- Target: the common compositum refinement maps below its left input
field. -/
def compositumWith_le_leftStatement
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) : Prop :=
  (M.compositumWith S).toSubgroup ≤ M.field.toSubgroup

/-- Target: the common compositum refinement maps below its right input
field. -/
def compositumWith_le_rightStatement
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) : Prop :=
  (M.compositumWith S).toSubgroup ≤ S.toSubgroup

end FiniteIntermediateField

end groupTheoreticRefinements

end
end Langlands.NYLL.ClassFormation
