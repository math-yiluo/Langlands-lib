/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitDescent.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# The unit norm range of a finite intermediate field

Modified by Worker 5264, 15 November 2026: extract the definition M050.001
`ValuationData.finiteIntermediateUnitNormRange` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source import by focused published imports, and
omit the rest of the source file, the unused `universe u` and the unused
`open CategoryTheory` and `open scoped BigOperators`. The binders, docstring
and body are unchanged. See the paired Markdown and `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The image `N_{M/K} U_M` from one finite intermediate field. -/
def finiteIntermediateUnitNormRange
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) := by
  letI : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field M.field M.below) :=
    M.finite
  exact ((relativeNorm A K.field M.field M.below).comp
    (v.unitAddSubgroup (M.toFiniteAbstractField K)).subtype).range

end ValuationData

end

end Langlands.NYLL.ClassFormation
