/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Target: the Frobenius exponent is additive

Modified by Worker 5264, 15 November 2026: state the source theorem M053.001
`DegreeData.frobeniusExponent_mul` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source imports by focused published imports, omit
the proof, the `@[simp]` attribute (a definition of a proposition is not a
simp lemma), the rest of the source file and the unused `open KummerTheory`
and `open CategoryTheory`. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

section frobeniusAlgebra

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: the exponent is additive under multiplication in the Frobenius
semigroup. -/
def frobeniusExponent_mulStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ₁ σ₂ : D.FrobeniusElements K L hLK) : Prop :=
    D.frobeniusExponent K L hLK (σ₁ * σ₂) =
      D.frobeniusExponent K L hLK σ₁ +
      D.frobeniusExponent K L hLK σ₂

end DegreeData

end frobeniusAlgebra

end

end Langlands.NYLL.ClassFormation
