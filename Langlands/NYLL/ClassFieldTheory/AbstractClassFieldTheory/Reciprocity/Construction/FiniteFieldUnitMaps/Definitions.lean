/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# Relative normality and finiteness across the residue-field enrichment

Modified by Worker 5264, 15 November 2026: extract the instances M045.001
`FiniteAbstractField.toFiniteResidueAbstractField_extensionNormal` and
M045.002 `FiniteAbstractField.toFiniteResidueAbstractField_extensionFinite`
of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean`
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

namespace FiniteAbstractField

/-- Normality transports across the canonical residue-field enrichment. -/
instance toFiniteResidueAbstractField_extensionNormal
    (K : FiniteAbstractField G) (D : DegreeData G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal] :
    (extensionSubgroup (K.toFiniteResidueAbstractField D).field L hLK).Normal := by
  change (extensionSubgroup K.field L hLK).Normal
  exact hnormal

/-- Relative finiteness transports across the canonical residue-field enrichment. -/
instance toFiniteResidueAbstractField_extensionFinite
    (K : FiniteAbstractField G) (D : DegreeData G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    Finite ((K.toFiniteResidueAbstractField D).field.toSubgroup ⧸
      extensionSubgroup (K.toFiniteResidueAbstractField D).field L hLK) := by
  change Finite
    (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)
  exact hfinite

end FiniteAbstractField

end

end Langlands.NYLL.ClassFormation
