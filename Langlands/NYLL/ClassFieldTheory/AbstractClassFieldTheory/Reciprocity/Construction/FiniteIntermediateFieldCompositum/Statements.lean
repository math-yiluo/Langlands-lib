/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteIntermediateFieldCompositum.Definitions

/-!
# NYLL M037.002–003: positivity and common composita of finite stages

Modified by Worker 483: extract the signatures of M037.002 and M037.003 from
the pinned NYLL FiniteIntermediateFieldCompositum.lean, prefix their
namespace with Langlands.NYLL, and replace each theorem with a Prop-valued
Statement definition. Preserve the universes, the full telescopes, binder
kinds and order. Omit the proofs. See the paired Markdown and
licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u v

section finiteIntermediateFields

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- Target: the finite quotient used in the descent construction has
positive cardinality. -/
def quotientCard_posStatement {E K : ClosedSubgroup G}
    (M : FiniteIntermediateField E K) : Prop :=
  0 < M.quotientCard

/-- Target: an initial finite stage and finitely many further stages have a
common finite overfield.  This existential form avoids choosing an
artificial ordering of the finite family. -/
def exists_common_compositumStatement {E K : ClosedSubgroup G} {ι : Type v}
    (M : FiniteIntermediateField E K) (s : Finset ι)
    (F : ι → FiniteIntermediateField E K) : Prop :=
  ∃ P : FiniteIntermediateField E K,
    P.field.toSubgroup ≤ M.field.toSubgroup ∧
      ∀ i ∈ s, P.field.toSubgroup ≤ (F i).field.toSubgroup

end FiniteIntermediateField

end finiteIntermediateFields

end
end Langlands.NYLL.ClassFormation
