/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.Definitions

/-!
# Targets: unit groups are preserved by inclusion and relative norm

Modified by Worker 5264, 15 November 2026: state the source theorems M045.007
`ValuationData.fixedFieldInclusion_mem_unitAddSubgroup` and M045.010
`ValuationData.relativeNorm_mem_unitAddSubgroup` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteFieldUnitMaps.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append
`Statement` to the names, omit the proofs, the rest of the source file and
the unused `universe u v`, `open KummerTheory`, `open CyclicCohomology`,
`open CategoryTheory` and `open scoped BigOperators`. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- Target: units stay units after inclusion into any finite extension.  The
construction uses this silently when all finitely many terms of `(*)` are
placed in one finite Galois field. -/
def fixedFieldInclusion_mem_unitAddSubgroupStatement
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.base) : Prop :=
    fixedFieldInclusion A E.base.field E.field.field E.below u.1 ∈
      v.unitAddSubgroup E.field

/-- Target: the norm of a unit through an arbitrary finite extension is a unit.
This is the valuation-theoretic step used when a finite Galois refinement
is pushed back down to the originally prescribed intermediate field. -/
def relativeNorm_mem_unitAddSubgroupStatement
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (u : v.unitAddSubgroup E.field) : Prop :=
    relativeNorm A E.base.field E.field.field E.below u.1 ∈
      v.unitAddSubgroup E.base

end ValuationData

end

end Langlands.NYLL.ClassFormation
