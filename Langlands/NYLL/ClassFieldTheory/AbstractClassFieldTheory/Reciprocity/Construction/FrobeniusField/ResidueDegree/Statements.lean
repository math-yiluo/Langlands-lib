/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FrobeniusField.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions

/-!
# Targets about the degree image of the Frobenius fixed field

Modified by Worker 5264, 15 November 2026: state the source theorems M016.015
`frobeniusFixedSubgroupWithin_normalizedDegree_image` and M016.018
`frobeniusFixedField_relativeResidueQuotientFinite` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, expand `extensionSubgroup K.field L hLK` to its exact Mathlib
body `L.toSubgroup.subgroupOf K.field.toSubgroup`, keep the source variable
declaration, parameters and binder kinds, and omit the proofs. See the
paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: the normalized-degree image of the actual subgroup `G_Σ ≤ G_K` is
the image already computed on the group-dual `Γ`. -/
def frobeniusFixedSubgroupWithin_normalizedDegree_imageStatement
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    (D.frobeniusFixedSubgroupWithin K L hLK σ).map
        (D.normalizedDegree K).toMonoidHom =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range

/-- Target: the actual relative residue quotient of the Frobenius fixed field over
`K` is finite.  Positivity of the computed mapped relative index gives an
honest finite-index witness before any natural-valued cardinality is formed. -/
def frobeniusFixedField_relativeResidueQuotientFiniteStatement
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Prop :=
    Finite
      (↥(K.field.toSubgroup.map D.degree.toMonoidHom) ⧸
        ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
            D.degree.toMonoidHom).subgroupOf
          (K.field.toSubgroup.map D.degree.toMonoidHom))

end DegreeData

end

end Langlands.NYLL.ClassFormation
