/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.CardinalFinitenessStatements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.U035.Proofs

/-!
# Finiteness of the relative ramification cardinal

Modified by Worker 183: extract NYLL M010.082, publish it under the
required PortInternal.M010.d082 name and use its published Statement
as its type. Keep the source finiteness arguments M010.079–080 private;
expand extensionSubgroup to its exact Subgroup.subgroupOf body.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData.FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

private theorem degreeCardinal_lt_aleph0 :
    E.toAbstractExtension.degreeCardinal < Cardinal.aleph0 := by
  change Cardinal.mk
      (E.base.toSubgroup ⧸ E.field.toSubgroup.subgroupOf E.base.toSubgroup) <
    Cardinal.aleph0
  exact Cardinal.lt_aleph0_of_finite _

private theorem relativeDegreeCardinals_lt_aleph0 (D : DegreeData G) :
    Cardinal.lift.{u}
          (E.toAbstractExtension.relativeResidueDegreeCardinal D) <
        Cardinal.aleph0 ∧
      E.toAbstractExtension.relativeRamificationIndexCardinal D <
        Cardinal.aleph0 := by
  have hresidueUnlifted :
      E.toAbstractExtension.relativeResidueDegreeCardinal D ≠ 0 := by
    rw [AbstractExtension.relativeResidueDegreeCardinal,
      relativeIndexCardinal, intersectionIndexCardinal]
    exact Cardinal.mk_ne_zero _
  have hresidue :
      Cardinal.lift.{u}
          (E.toAbstractExtension.relativeResidueDegreeCardinal D) ≠ 0 := by
    intro hzero
    exact hresidueUnlifted (Cardinal.lift_eq_zero.mp hzero)
  have hramification :
      E.toAbstractExtension.relativeRamificationIndexCardinal D ≠ 0 := by
    rw [AbstractExtension.relativeRamificationIndexCardinal,
      relativeIndexCardinal, intersectionIndexCardinal]
    exact Cardinal.mk_ne_zero _
  apply (Cardinal.mul_lt_aleph0_iff_of_ne_zero
    hresidue hramification).mp
  rw [← (open Langlands.NYLL.ClassFormation.DegreeData.AbstractExtension in
    degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal
      E.toAbstractExtension D)]
  exact E.degreeCardinal_lt_aleph0

/-- The relative ramification cardinal of a finite abstract extension is finite. -/
theorem _root_.Langlands.NYLL.PortInternal.M010.d082
    (D : DegreeData G) :
    Langlands.NYLL.PortInternal.M010.d082Statement E D :=
  (E.relativeDegreeCardinals_lt_aleph0 D).2

end DegreeData.FiniteAbstractExtension
end Langlands.NYLL.ClassFormation
