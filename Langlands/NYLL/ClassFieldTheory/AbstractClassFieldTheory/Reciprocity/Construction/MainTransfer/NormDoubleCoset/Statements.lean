/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.NormWitness.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.Intermediate.U003.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransferFrobeniusGeometry.GroupOnly.U003.Proofs

/-!
# NYLL transfer norm double-coset identity target

Modified by Worker 196, 14 November 2026: extract the theorem type of M071.024
(MainTransfer.lean:722–740) at fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with `Langlands.NYLL`, use focused published imports,
expand `extensionSubgroup` to its exact Mathlib body, and record the theorem
as a Prop-valued definition. Both source local-instance proof terms are retained.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

-- Retain the source Representation section's universe-zero group alias.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The additive norm identity for the chosen right-transversal witness. -/
def transferNormNaturality_norm_doubleCoset_formulaStatement
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : ((L.toSubgroup.subgroupOf K.toSubgroup)).Normal]
    [Finite (K.toSubgroup ⧸
      (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A L) : Prop :=
    letI : ((L.toSubgroup.subgroupOf K'.toSubgroup)).Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hLK' hK'K
    letI : Finite (K'.toSubgroup ⧸ (L.toSubgroup.subgroupOf K'.toSubgroup)) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hLK' hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hLK' hK'K)
    fixedFieldInclusion A K K' hK'K
        (relativeNorm A K L (hLK'.trans hK'K) a) =
      relativeNorm A K' L hLK'
        (transferNormNaturalityNormWitness A K K' L hLK' hK'K a)

end
end Langlands.NYLL.ClassFormation
