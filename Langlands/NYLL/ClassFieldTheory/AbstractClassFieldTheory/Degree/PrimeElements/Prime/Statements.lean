/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions

/-!
# Targets for units, unramified inclusions and prime elements

Modified by Worker 5264, 15 November 2026: extract the statements of
M028.009, M028.010, M028.011 and M028.012 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and replace the source module import by the published
prime-element, fixed-field-inclusion, finite-field-extension and relative-norm
modules. Replace each source theorem by a Prop-valued definition with the
`Statement` suffix, omitting its proof and the `@[simp]` attribute of
M028.009, and reword each declaration docstring to describe the proposition.
The three targets whose hypothesis binders do not occur in the proposition are
preceded by `set_option linter.unusedVariables false in`, which keeps the
source binder names. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- The proposition, from the source theorem `mem_unitAddSubgroup_iff`, that
`u` lies in the additive unit group `U_K` exactly when `v.valuationAt K u = 0`. -/
def mem_unitAddSubgroup_iffStatement (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (u : ambientFixedAddSubgroup A K.field) : Prop :=
    u ∈ v.unitAddSubgroup K ↔ v.valuationAt K u = 0

set_option linter.unusedVariables false in
/-- The proposition, from the source theorem
`valuationAt_fixedFieldInclusion_of_unramified`, that over an unramified
extension the normalized valuation restricts to the valuation below. -/
def valuationAt_fixedFieldInclusion_of_unramifiedStatement
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hUn : E.IsUnramified D)
    (a : ambientFixedAddSubgroup A E.base.field) : Prop :=
    v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below a) =
      v.valuationAt E.base a

set_option linter.unusedVariables false in
/-- The proposition, from the source theorem `prime_of_unramified`, that a
prime element remains prime in an unramified extension. -/
def prime_of_unramifiedStatement (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hUn : E.IsUnramified D)
    (π : ambientFixedAddSubgroup A E.base.field)
    (hπ : v.IsPrimeElement E.base π) : Prop :=
    v.IsPrimeElement E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below π)

set_option linter.unusedVariables false in
/-- The proposition, from the source theorem `norm_prime_of_totallyRamified`,
that in a totally ramified extension the norm of a prime element is prime. -/
def norm_prime_of_totallyRamifiedStatement (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (π : ambientFixedAddSubgroup A E.field.field) : Prop :=
    v.IsPrimeElement E.field π →
      v.IsPrimeElement E.base
        (relativeNorm A E.base.field E.field.field E.below π)

end ValuationData

end

end Langlands.NYLL.ClassFormation
