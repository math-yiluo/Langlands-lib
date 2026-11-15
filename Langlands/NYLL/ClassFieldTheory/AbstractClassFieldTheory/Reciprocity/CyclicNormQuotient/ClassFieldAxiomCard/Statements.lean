/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Targets: the order of a cyclic norm quotient under the class-field axiom

Modified by Worker 5264, 15 November 2026: state the source theorems M074.010
`finiteNormQuotientFiniteOfClassFieldAxiom`, M074.011
`finiteNormQuotient_card_of_classFieldAxiom`, M074.012
`additiveExtensionQuotient_card`, M074.013 `cyclicReciprocity_card_equality`
and M074.014 `finiteNormQuotient_finite_of_classFieldAxiom` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, replace the source imports by focused published imports, omit
the proofs, the rest of the source file and the unused `open KummerTheory`
and `open CategoryTheory`, and turn off the unused-variable linter for the
hypotheses `hcf`, `hKfinite`, `hnormal` and `hg`, which the propositions do
not mention. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

set_option linter.unusedVariables false in
/-- Target: the class-field axiom first gives genuine finiteness of the
actual norm quotient, transported from finite degree-zero Tate cohomology. -/
def finiteNormQuotientFiniteOfClassFieldAxiomStatement
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
    Finite (FiniteNormQuotient A E.base E.field E.below)

set_option linter.unusedVariables false in
/-- Target: the class-field axiom gives the exact order of the actual norm
quotient in the cyclic case. -/
def finiteNormQuotient_card_of_classFieldAxiomStatement
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
    Nat.card (FiniteNormQuotient A E.base E.field E.below) =
      (E.degree : ℕ)

/-- Target: the additive Galois quotient has the extension degree as its
order. -/
def additiveExtensionQuotient_cardStatement
    (E : DegreeData.FiniteAbstractExtension G) : Prop :=
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below)) =
      (E.degree : ℕ)

set_option linter.unusedVariables false in
/-- Target: under the class-field axiom, the cyclic Galois quotient and its
actual norm quotient have the same finite order. -/
def cyclicReciprocity_card_equalityStatement
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below)) =
      Nat.card (FiniteNormQuotient A E.base E.field E.below)

set_option linter.unusedVariables false in
/-- Target: the cyclic norm quotient is finite as an actual type under the
class-field axiom. -/
def finiteNormQuotient_finite_of_classFieldAxiomStatement
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
    Finite (FiniteNormQuotient A E.base E.field E.below)

end

end Langlands.NYLL.ClassFormation
