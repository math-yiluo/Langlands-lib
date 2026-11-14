/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation.FixedCarrier.Definitions

/-!
# NYLL M083: the `H⁻¹` primitive of a difference with equal norms

Modified by Worker 171: the source theorem M083.004
`ClassFormation.ValuationData.abstractReciprocity_exists_hMinusOne_primitive` of the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean`
becomes the Prop-valued target
`abstractReciprocity_exists_hMinusOne_primitiveStatement`, whose body is the
source conclusion, with the source section variables and every source
hypothesis in the source order; the proof is omitted. The namespace is
prefixed with `Langlands.NYLL`, the source module import is replaced by
focused published imports, and the unused-variable linter is silenced for the
hypotheses `hcf`, `hg` and `hnorm`, which the conclusion does not mention.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open CategoryTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

set_option linter.unusedVariables false in
/-- Target for M083.004.  The class-field axiom, in representative form:
equality of two actual relative norms yields the element `a` for which
`a^σ-a = v-u`. -/
def abstractReciprocity_exists_hMinusOne_primitiveStatement
    (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (extensionSubgroup
      E.base.field E.field.field E.below).Normal)
    (g : E.base.field.toSubgroup ⧸
      extensionSubgroup E.base.field E.field.field E.below)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (u w : ambientFixedAddSubgroup A E.field.field)
    (hnorm : relativeNorm A E.base.field E.field.field E.below w =
      relativeNorm A E.base.field E.field.field E.below u) : Prop :=
    let M := extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal
    ∃ a : M.V,
      M.ρ g a - a =
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal).symm
          (w - u)

end ValuationData

end
end Langlands.NYLL.ClassFormation
