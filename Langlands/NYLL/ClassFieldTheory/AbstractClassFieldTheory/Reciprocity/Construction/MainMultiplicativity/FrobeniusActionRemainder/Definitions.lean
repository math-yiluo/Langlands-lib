/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# The Frobenius action remainder

Modified by Worker 5264, 15 November 2026: extract the definition M053.003
`DegreeData.frobeniusActionRemainder` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by focused published imports,
and omit the rest of the source file and the unused `open KummerTheory`
and `open CategoryTheory`. The universe, binders, docstring and body are
unchanged. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- For the left `Rep` action, the remainder corresponding to the
right-action notation is `φⁿσ⁻¹`. -/
def frobeniusActionRemainder (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK) :
    K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
  φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹

end DegreeData

end

end Langlands.NYLL.ClassFormation
