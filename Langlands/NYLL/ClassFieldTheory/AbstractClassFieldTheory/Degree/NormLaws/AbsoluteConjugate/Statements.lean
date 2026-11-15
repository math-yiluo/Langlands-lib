/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.AbsoluteConjugate.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.ConjugateFixedElement.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions

/-!
# Targets: absolute conjugate cosets and the conjugated absolute norm

Modified by Worker 5264, 15 November 2026: state the source theorems
M026.008 `absoluteConjugateCosetEquiv_mk` and M026.010
`relativeNorm_absoluteConjugate_apply` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the names, replace the source imports by focused published imports and
the imports of the M026.003 and M026.007 definitions, and refer to the
private source definition `absoluteConjugationEquiv` (M026.005) by its
published name `Langlands.NYLL.PortInternal.M026.d005`. The source opens,
variable declaration, binders and statements (including the `letI` of
M026.010) are unchanged; the proofs, the `@[simp]` attribute of M026.008
and the rest of the source file are omitted. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators Pointwise

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Target: establishes the identity
`absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) = QuotientGroup.mk
(absoluteConjugationEquiv σ x)`, where the private source definition
`absoluteConjugationEquiv` is published as
`Langlands.NYLL.PortInternal.M026.d005`. -/
def absoluteConjugateCosetEquiv_mkStatement
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G)
    (x : (baseField G).toSubgroup) : Prop :=
    absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) =
      QuotientGroup.mk (Langlands.NYLL.PortInternal.M026.d005 σ x)

/-- Target: conjugation compatibility of normalized valuations: the absolute
norm commutes with conjugation.

The construction writes the action on fields and elements on the right.  Thus the
left action used by `Rep` realizes `a^σ` as `ρ(σ⁻¹)a`. -/
def relativeNorm_absoluteConjugate_applyStatement [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    [Finite
      ((baseField G).toSubgroup ⧸
        extensionSubgroup (baseField G) K
          (le_baseField K))]
    (a : ambientFixedAddSubgroup A K) : Prop :=
    letI : Finite
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G)
            (conjugateClosedSubgroup K σ)
            (le_baseField (conjugateClosedSubgroup K σ))) :=
      Finite.of_equiv
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) K
            (le_baseField K))
        (absoluteConjugateCosetEquiv K σ).symm
    ((relativeNorm A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) :
      ambientFixedAddSubgroup A (baseField G)) : A.V) =
      A.ρ σ⁻¹
        ((relativeNorm A (baseField G) K
          (le_baseField K) a :
          ambientFixedAddSubgroup A (baseField G)) : A.V)

end

end Langlands.NYLL.ClassFormation
