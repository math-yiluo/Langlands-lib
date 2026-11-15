/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitDescent.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions

/-!
# Finite-stage units of an infinite extension

Modified by Worker 5264, 15 November 2026: extract the definition M049.004
`ValuationData.IsFiniteStageUnit` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitDescent.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by focused published imports, and
omit the rest of the source file, the unused `universe u v` and the unused
`open CyclicCohomology`, `open CategoryTheory` and `open scoped BigOperators`.
The binders, docstring and body are unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- An element of an infinite algebraic extension is a unit when it is
already a unit at some finite intermediate stage.  This is the literal
finite-support meaning of `U_E = \bigcup_M U_M` used. -/
def IsFiniteStageUnit
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A E) : Prop :=
  ∃ M : FiniteIntermediateField E K.field,
    ∃ u : v.unitAddSubgroup (M.toFiniteAbstractField K),
      fixedFieldInclusion A M.field E M.above u.1 = a

end ValuationData

end

end Langlands.NYLL.ClassFormation
