/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.Definitions
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U002.Definitions

/-!
# Targets about the normalized degree on the Frobenius closure

Modified by Worker 5264, 15 November 2026: state the source theorems M014.029
`frobeniusClosureDegree_generator` and M014.030
`frobeniusClosureDegree_range` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, expand `extensionSubgroup K.field L hLK` to its exact Mathlib
body `L.toSubgroup.subgroupOf K.field.toSubgroup`, keep the source universe
and variable declarations, parameters and binder kinds, and omit the proofs
and the `@[simp]` attribute. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: the degree map sends the canonical Frobenius-closure generator to its expected
value. -/
def frobeniusClosureDegree_generatorStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    D.frobeniusClosureDegree K L hLK σ
        (D.frobeniusInClosure K L hLK σ) =
      (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK σ

/-- Target: the image of `d_K` on `Γ` is precisely `n ℤ̂`, where
`n = d_K(σ)`.  This is the group-dual residue-degree calculation in
the Frobenius fixed-field residue-degree formula. -/
def frobeniusClosureDegree_rangeStatement (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range =
      AddSubgroup.toSubgroup
        ((zHatMulNat (D.frobeniusExponent K L hLK σ)).toAddMonoidHom.range)

end DegreeData

end
end Langlands.NYLL.ClassFormation
