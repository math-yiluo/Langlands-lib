/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.NormalCoreField.Definitions

/-!
# Targets: the normal core field lies below `K` and `M`, and represents the normal core

Modified by Worker 5264, 15 November 2026: state the source theorems M033.002
`FiniteIntermediateField.normalCoreField_le`, M033.003
`FiniteIntermediateField.normalCoreField_le_field` and M033.004
`FiniteIntermediateField.extensionSubgroup_normalCoreField` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, replace the source imports by the focused published import,
and omit the proofs and the rest of the source file. In M033.004 the proof
term `M.normalCoreField_le` (the unpublished proof of M033.002) is replaced by
the source proof of M033.002 written inline; by proof irrelevance the
proposition is the same. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

section groupTheoreticRefinements

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- Target: the normal core field lies below the field from which it is
constructed. -/
def normalCoreField_leStatement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) : Prop :=
  (M.normalCoreField).toSubgroup ≤ K.toSubgroup

/-- Target: the normal core is contained in the specified refinement field. -/
def normalCoreField_le_fieldStatement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) : Prop :=
  (M.normalCoreField).toSubgroup ≤ M.field.toSubgroup

/-- Target: the subgroup representing the normal core field is the
corresponding normal core. -/
def extensionSubgroup_normalCoreFieldStatement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K) : Prop :=
  extensionSubgroup K M.normalCoreField
      (show (M.normalCoreField).toSubgroup ≤ K.toSubgroup by
        rintro g ⟨k, _, rfl⟩
        exact k.2) =
    (extensionSubgroup K M.field M.below).normalCore

end FiniteIntermediateField

end groupTheoreticRefinements

end

end Langlands.NYLL.ClassFormation
