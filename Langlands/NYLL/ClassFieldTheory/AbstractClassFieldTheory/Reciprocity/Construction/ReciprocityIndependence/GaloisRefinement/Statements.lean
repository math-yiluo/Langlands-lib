/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.GaloisRefinement.Definitions

/-!
# Target: a Galois refinement lies below the original finite field

Modified by Worker 5264, 15 November 2026: state the source theorem M033.006
`FiniteIntermediateField.galoisRefinement_le_field` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source imports by the focused published import,
and omit the proof and the rest of the source file. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

section groupTheoreticRefinements

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- Target: a Galois refinement lies below the original finite field. -/
def galoisRefinement_le_fieldStatement [IsTopologicalGroup G]
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    [_hEnormal :
      (extensionSubgroup K E (M.above.trans M.below)).Normal] : Prop :=
  (M.galoisRefinement).field.toSubgroup ≤ M.field.toSubgroup

end FiniteIntermediateField

end groupTheoreticRefinements

end

end Langlands.NYLL.ClassFormation
