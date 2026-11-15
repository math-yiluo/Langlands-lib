/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Statements

/-!
# Targets about the field fixed by a Frobenius lift

Modified by Worker 5264: state the source theorems M016.002
`mem_frobeniusFixedSubgroupWithin_iff`, M016.003
`frobeniusFixedSubgroupWithin_isClosed`, M016.005 `mem_frobeniusFixedField_iff`,
M016.006 `frobeniusFixedField_le`, M016.007
`extensionSubgroup_frobeniusFixedField`, M016.008
`extensionInertiaWithin_le_frobeniusFixedSubgroupWithin`, M016.009
`fieldInertia_le_frobeniusFixedField`, M016.010 `frobeniusFixedField_finite`,
M016.012 `frobeniusFixedField_index_le_extensionIndex_of_exponent_eq_one`,
M016.013 `frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin` and M016.014
`frobeniusFixedField_fieldInertia` of the pinned NYLL FrobeniusField source as
Prop-valued Statement definitions. Prefix the namespace with Langlands.NYLL,
append `Statement` to each name, expand `extensionSubgroup` to its exact Mathlib
body `Subgroup.subgroupOf` (this drops its unused inclusion-proof argument, so
the theorem M016.006 `frobeniusFixedField_le`, which the source passes as that
argument, does not occur in the statements of M016.007, M016.010 and
M016.012), keep the source variable declaration, parameters and binder kinds,
and omit the proofs and the `@[simp]` attributes. The option
`linter.unusedVariables` is disabled for the M016.010 and M016.012 targets,
whose source hypotheses are used only by the omitted proofs.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: membership in the internal Frobenius-fixed subgroup is characterized by
fixedness under Frobenius. -/
def mem_frobeniusFixedSubgroupWithin_iffStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) (k : K.field.toSubgroup) : Prop :=
    k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ↔
      QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup

/-- Target: the Frobenius-fixed subgroup inside the extension subgroup is closed. -/
def frobeniusFixedSubgroupWithin_isClosedStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    IsClosed
      (D.frobeniusFixedSubgroupWithin K L hLK σ : Set K.field.toSubgroup)

/-- Target: an element lies in the Frobenius fixed field exactly when Frobenius fixes its
restriction. -/
def mem_frobeniusFixedField_iffStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) (g : G) : Prop :=
    g ∈ D.frobeniusFixedField K L hLK σ ↔
      ∃ k : K.field.toSubgroup,
        k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ∧ k.1 = g

/-- Target: the field `Σ` extends `K`, i.e. `G_Σ ≤ G_K`. -/
def frobeniusFixedField_leStatement (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤ K.field.toSubgroup

/-- Target: inside `G_K`, the subgroup attached to the actual field `Σ` is
literally the quotient-projection inverse image used in its definition. -/
def extensionSubgroup_frobeniusFixedFieldStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup =
      D.frobeniusFixedSubgroupWithin K L hLK σ

/-- Target: the subgroup `I_L = G_{\widetilde L}` lies in `G_Σ`. -/
def extensionInertiaWithin_le_frobeniusFixedSubgroupWithinStatement
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    D.extensionInertiaWithin K.field L hLK ≤
      D.frobeniusFixedSubgroupWithin K L hLK σ

/-- Target: ambient form of `I_L ≤ G_Σ`. -/
def fieldInertia_le_frobeniusFixedFieldStatement (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    (D.fieldInertia L).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup

set_option linter.unusedVariables false in
/-- Target: finiteness of the Frobenius fixed field on the actual field side: `Σ | K` is
finite. -/
def frobeniusFixedField_finiteStatement (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    Finite
      (K.field.toSubgroup ⧸
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup)

set_option linter.unusedVariables false in
/-- Target: finiteness of the Frobenius fixed field, with the index estimate from the proof
exposed on the actual-field side.  For a degree-one lift, `[Σ : K] ≤ [L : K]`. -/
def frobeniusFixedField_index_le_extensionIndex_of_exponent_eq_oneStatement
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK)
    (hσ : D.frobeniusExponent K L hLK σ = 1) : Prop :=
    ((D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf K.field.toSubgroup).index ≤
      (L.toSubgroup.subgroupOf K.field.toSubgroup).index

/-- Target: the procyclic degree isomorphism, faithfully pulled back along
`G_K → G_K / I_L`: `G_Σ ∩ I_K = I_L`.  This is the subgroup form of
the equality `\widetilde Σ = \widetilde L`. -/
def frobeniusFixedSubgroupWithin_inf_fieldInertiaWithinStatement
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    D.frobeniusFixedSubgroupWithin K L hLK σ ⊓
        D.fieldInertiaWithin K.field =
      D.extensionInertiaWithin K.field L hLK

/-- Target: ambient version of the procyclic degree isomorphism: the maximal unramified
extensions of `Σ` and `L` have the same absolute Galois subgroup. -/
def frobeniusFixedField_fieldInertiaStatement (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    D.fieldInertia (D.frobeniusFixedField K L hLK σ) =
      D.fieldInertia L

end DegreeData

end
end Langlands.NYLL.ClassFormation
