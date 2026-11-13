/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U041.Proofs

/-!
# NYLL M010: bundling a finite inclusion over a finite field

Modified by Worker 171: extract M010.131 from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, prefix
the namespace with `Langlands.NYLL`, and replace the source module imports by
focused published imports. Universes, binders, attributes, fields and the
construction are otherwise unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbstractFieldExtension

/-- Canonically bundle a finite relative extension of a field already finite
over the distinguished base.  Finiteness of the upper field follows from the
actual quotient tower. -/
@[implicit_reducible]
noncomputable def ofInclusion (field : ClosedSubgroup G)
    (base : FiniteAbstractField G)
    (below : field.toSubgroup ≤ base.field.toSubgroup)
    [finiteQuotient : Finite
      (base.field.toSubgroup ⧸
        extensionSubgroup base.field field below)] :
    FiniteAbstractFieldExtension G where
  field := {
    field := field
    finite := by
      apply Cardinal.lt_aleph0_iff_finite.mp
      let T : DegreeData.AbstractExtension.Tower G := {
        top := field
        middle := base.field
        base := baseField G
        top_le_middle := below
        middle_le_base := le_baseField base.field }
      change T.totalExtension.degreeCardinal < Cardinal.aleph0
      rw [← T.degreeCardinal_mul]
      apply Cardinal.mul_lt_aleph0
      · change Cardinal.mk
          (base.field.toSubgroup ⧸
            extensionSubgroup base.field field below) < Cardinal.aleph0
        exact Cardinal.lt_aleph0_of_finite _
      · change Cardinal.mk
          ((baseField G).toSubgroup ⧸
            extensionSubgroup (baseField G) base.field
              (le_baseField base.field)) < Cardinal.aleph0
        exact Cardinal.lt_aleph0_of_finite _ }
  base := base
  below := below
  finiteQuotient := finiteQuotient

end FiniteAbstractFieldExtension

end
end Langlands.NYLL.ClassFormation
