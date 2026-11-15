/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.FrobeniusTower.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Target: the Frobenius tower map multiplies normalized degree by `f`

Modified by Worker 5264, 15 November 2026: state the source theorem M066.006
`DegreeData.finiteReciprocityNaturalityFrobeniusTowerMap_degree` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source import by focused published imports, and
omit the proof, the rest of the source file and the unused
`open KummerTheory`, `open CategoryTheory` and `open scoped BigOperators`.
See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: Frobenius residue-degree compatibility's normalized-degree square
on the two infinite Frobenius quotients. -/
def finiteReciprocityNaturalityFrobeniusTowerMap_degreeStatement
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.FiniteResidueAbstractExtension D)
    (L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ E.base.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ E.field.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup E.base.field L hLK).Normal]
    [hL'normal : (extensionSubgroup E.field.field L' hL'K').Normal]
    (q : E.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L' hL'K') : Prop :=
    (D.extensionNormalizedDegree E.base L hLK
      (D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L'
        hLK hL'K' E.below hL'L q)).toAdd =
      (E.residueDegree : ℕ) •
        (D.extensionNormalizedDegree E.field L' hL'K' q).toAdd

end DegreeData

end

end Langlands.NYLL.ClassFormation
