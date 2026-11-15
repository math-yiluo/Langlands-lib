/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.OfInclusion
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# The finite-field extension bundle of a finite intermediate field

Modified by Worker 5264, 15 November 2026: extract the definitions M049.001
`FiniteIntermediateField.toFiniteAbstractFieldExtension` and M049.002
`FiniteIntermediateField.toFiniteAbstractField` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by focused published imports,
and omit the rest of the source file and the unused `universe u v`,
`open KummerTheory`, `open CategoryTheory` and `open scoped BigOperators`.
The binders, docstrings and bodies are unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- The canonical finite-field extension bundle carried by a finite
intermediate field over a bundled finite base. -/
noncomputable def toFiniteAbstractFieldExtension
    {E : ClosedSubgroup G} (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) :=
    M.finite
  exact FiniteAbstractFieldExtension.ofInclusion M.field K M.below

/-- The upper endpoint of the canonical finite-field extension bundle. -/
noncomputable def toFiniteAbstractField
    {E : ClosedSubgroup G} (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) : FiniteAbstractField G :=
  (M.toFiniteAbstractFieldExtension K).field

end FiniteIntermediateField

end

end Langlands.NYLL.ClassFormation
