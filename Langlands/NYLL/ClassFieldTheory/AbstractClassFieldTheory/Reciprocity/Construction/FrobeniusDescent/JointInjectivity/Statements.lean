/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.FrobeniusElements.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusSemigroup.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Targets: restriction and normalized degree distinguish Frobenius elements

Modified by Worker 5264, 15 November 2026: state the source theorems
M017.005 `extensionRestriction_normalizedDegree_joint_injective`, M017.006
`frobeniusRestriction_mul` and M017.007
`frobenius_eq_of_restriction_eq_of_degree_eq` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the names, replace the source imports by focused published imports, keep
the source open, variable declaration, parameters, binder kinds and
statements unchanged, and omit the proofs, the `@[simp]` attribute of
M017.006 and the rest of the source file. The multiplication of Frobenius
elements in M017.006 is the published instance M015.002
`frobeniusElementsMul`. The unused-variable linter is turned off for M017.007,
whose hypotheses `hRestriction` and `hDegree` the proposition does not
mention. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: restriction and normalized degree jointly distinguish elements of
`G(\widetilde L/K)`. -/
def extensionRestriction_normalizedDegree_joint_injectiveStatement
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] : Prop :=
    Function.Injective (fun q :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK =>
      (D.extensionRestriction K.field L hLK q,
        D.extensionNormalizedDegree K L hLK q))

/-- Target:
`frobeniusRestriction` satisfies the multiplication formula `D.frobeniusRestriction K L hLK (σ *
τ) = D.frobeniusRestriction K L hLK σ * D.frobeniusRestriction K L hLK τ`.
-/
def frobeniusRestriction_mulStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ τ : D.FrobeniusElements K L hLK) : Prop :=
    D.frobeniusRestriction K L hLK (σ * τ) =
      D.frobeniusRestriction K L hLK σ *
        D.frobeniusRestriction K L hLK τ

set_option linter.unusedVariables false in
/-- Target: Frobenius elements with equal restriction and equal normalized
degree are equal. -/
def frobenius_eq_of_restriction_eq_of_degree_eqStatement
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    {σ τ : D.FrobeniusElements K L hLK}
    (hRestriction :
      D.frobeniusRestriction K L hLK σ =
        D.frobeniusRestriction K L hLK τ)
    (hDegree :
      D.extensionNormalizedDegree K L hLK σ.1 =
        D.extensionNormalizedDegree K L hLK τ.1) : Prop :=
    σ = τ

end DegreeData

end

end Langlands.NYLL.ClassFormation
