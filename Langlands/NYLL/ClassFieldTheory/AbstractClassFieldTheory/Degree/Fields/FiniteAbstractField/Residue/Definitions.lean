/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.U081.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U011.Proofs

/-!
# NYLL M010: residue data of fields finite over the distinguished base

Modified by Worker 171: extract M010.126, M010.127 and M010.140 from the
pinned NYLL `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
prefix the namespace with `Langlands.NYLL`, and replace the source module
imports by focused published imports. In the proof of M010.126 the source
lemma `relativeResidueDegreeCardinal_lt_aleph0` (M010.081) is used under its
published name `Langlands.NYLL.PortInternal.M010.d081`, whose type is the
published Prop `Langlands.NYLL.PortInternal.M010.d081Statement`; that name is
therefore added to the `simpa only` set. Universes, binders, attributes,
fields and bodies are otherwise unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbstractField

/-- A finite field over the distinguished base has a finite absolute residue
quotient.  This is derived from the finite relative quotient and the
surjectivity of the ambient degree map. -/
@[implicit_reducible]
noncomputable def toFiniteResidueAbstractField
    (K : FiniteAbstractField G) (D : DegreeData G) :
    DegreeData.FiniteResidueAbstractField D where
  field := K.field
  finiteResidueQuotient := by
    apply Cardinal.lt_aleph0_iff_finite.mp
    change
      intersectionIndexCardinal (D.fieldImage K.field)
        (⊤ : Subgroup ZHatMul) < Cardinal.aleph0
    rw [D.fieldImage_eq_map]
    have htop :
        (baseField G).toSubgroup.map D.degree.toMonoidHom = ⊤ := by
      rw [baseField_toSubgroup]
      exact Subgroup.map_top_of_surjective _ D.degree_surjective
    rw [← htop]
    simpa only [FiniteAbstractField.toFiniteAbstractExtension,
      DegreeData.AbstractExtension.relativeResidueDegreeCardinal, relativeIndexCardinal,
      Langlands.NYLL.PortInternal.M010.d081Statement] using
      Langlands.NYLL.PortInternal.M010.d081 K.toFiniteAbstractExtension D

/-- The positive absolute residue degree of a field finite over the
distinguished base. -/
noncomputable def residueDegree (K : FiniteAbstractField G)
    (D : DegreeData G) : ℕ+ :=
  (K.toFiniteResidueAbstractField D).residueDegree

end FiniteAbstractField

namespace FiniteAbstractFieldExtension

/-- Canonically enrich both endpoints with their finite residue quotients. -/
noncomputable def toFiniteResidueAbstractExtension
    (E : FiniteAbstractFieldExtension G) (D : DegreeData G) :
    DegreeData.FiniteResidueAbstractExtension D where
  field := E.field.toFiniteResidueAbstractField D
  base := E.base.toFiniteResidueAbstractField D
  below := E.below
  finiteQuotient := E.finiteQuotient

end FiniteAbstractFieldExtension

end
end Langlands.NYLL.ClassFormation
