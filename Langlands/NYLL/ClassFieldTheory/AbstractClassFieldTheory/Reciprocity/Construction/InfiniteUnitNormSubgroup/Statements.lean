/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.InfiniteUnitNormSubgroup.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.InfiniteNorm.Definitions

/-!
# Targets: unit norm ranges of finite intermediate fields

Modified by Worker 5264, 15 November 2026: state the source theorems M050.002
`ValuationData.mem_finiteIntermediateUnitNormRange_of_overfield` and M050.005
`ValuationData.finiteIntermediateUnitNormRange_le_normRange` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/InfiniteUnitNormSubgroup.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, replace the source import by focused published imports, omit
the proofs, the rest of the source file, the unused `universe u` and the
unused `open CategoryTheory` and `open scoped BigOperators`, and turn off the
unused-variable linter for the hypotheses `hPM`, `hPfinite` and `haK`, which
the M050.002 proposition does not mention. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

set_option linter.unusedVariables false in
/-- Target: a unit norm obtained from a finite overfield of `M` already lies
in the unit norm range attached to `M`, by transitivity of the actual norm. -/
def mem_finiteIntermediateUnitNormRange_of_overfieldStatement
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M P : FiniteIntermediateField E K.field)
    (hPM : P.field.toSubgroup ≤ M.field.toSubgroup)
    [hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below)]
    (uP : v.unitAddSubgroup (P.toFiniteAbstractField K))
    (aK : ambientFixedAddSubgroup A K.field)
    (haK : relativeNorm A K.field P.field P.below uP.1 = aK) : Prop :=
    aK ∈ v.finiteIntermediateUnitNormRange E K M

/-- Target: proves the bound
`v.finiteIntermediateUnitNormRange E K M ≤ finiteIntermediateNormRange A E K.field M`. -/
def finiteIntermediateUnitNormRange_le_normRangeStatement
    (v : ValuationData D A) (E : ClosedSubgroup G)
    (K : FiniteAbstractField G)
    (M : FiniteIntermediateField E K.field) : Prop :=
    v.finiteIntermediateUnitNormRange E K M ≤
      finiteIntermediateNormRange A E K.field M

end ValuationData

end

end Langlands.NYLL.ClassFormation
