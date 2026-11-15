/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateCompositum.Compositum.Definitions

/-!
# Targets: the compositum lies below both finite intermediate fields

Modified by Worker 5264, 15 November 2026: state the source theorems M034.002
`FiniteIntermediateField.compositum_le_left` and M034.003
`FiniteIntermediateField.compositum_le_right` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteIntermediateCompositum.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, replace the source import by the focused published import,
and omit the proofs and the rest of the source file. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- Target: the bound
`(M.compositum N).field.toSubgroup ≤ M.field.toSubgroup`. -/
def compositum_le_leftStatement {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) : Prop :=
  (M.compositum N).field.toSubgroup ≤ M.field.toSubgroup

/-- Target: the bound
`(M.compositum N).field.toSubgroup ≤ N.field.toSubgroup`. -/
def compositum_le_rightStatement {E K : ClosedSubgroup G}
    (M N : FiniteIntermediateField E K) : Prop :=
  (M.compositum N).field.toSubgroup ≤ N.field.toSubgroup

end FiniteIntermediateField

end

end Langlands.NYLL.ClassFormation
