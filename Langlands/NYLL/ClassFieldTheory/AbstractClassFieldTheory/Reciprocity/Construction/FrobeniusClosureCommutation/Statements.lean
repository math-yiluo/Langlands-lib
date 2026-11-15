/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Definitions

/-!
# Targets: commutation with the Frobenius closure and the conjugated fixed field

Modified by Worker 5264, 15 November 2026: state the source theorems M042.001
`frobeniusClosure_commutes_of_commutes_generator` and M042.002
`conjugate_frobeniusFixedField_eq_of_commutes` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusClosureCommutation.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the names, expand `extensionSubgroup K.field L hLK` to its exact Mathlib
body `L.toSubgroup.subgroupOf K.field.toSubgroup`, keep the source universe,
variable declaration, parameters and binder kinds, omit the proofs and the
unused `open KummerTheory`, `open CyclicCohomology`, `open CategoryTheory` and
`open scoped BigOperators`, and turn off the unused-variable linter for the
commutation hypothesis `hq`, which the conclusions do not mention. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

noncomputable section

section frobeniusClosureCommutation

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

set_option linter.unusedVariables false in
/-- Target: commuting with the chosen Frobenius generator means commuting with
every element of the closed subgroup it topologically generates. -/
def frobeniusClosure_commutes_of_commutes_generatorStatement (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q)
    (c : D.frobeniusClosure K L hLK σ) : Prop :=
    q * c.1 = c.1 * q

set_option linter.unusedVariables false in
/-- Target: if a quotient element commutes with the Frobenius lift, its chosen
representative stabilizes the corresponding fixed field. -/
def conjugate_frobeniusFixedField_eq_of_commutesStatement (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : q * σ.1 = σ.1 * q) : Prop :=
    let k : K.field.toSubgroup := Quotient.out q
    conjugateClosedSubgroup (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
      D.frobeniusFixedField K L hLK σ

end DegreeData

end frobeniusClosureCommutation

end

end Langlands.NYLL.ClassFormation
