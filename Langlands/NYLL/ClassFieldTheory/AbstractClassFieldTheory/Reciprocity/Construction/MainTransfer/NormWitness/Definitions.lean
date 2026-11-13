/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.FixedCarrier.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainTransfer.RightTransversal.Definitions

/-!
# NYLL transfer norm witness

Modified by Worker 196, 13 November 2026: extract M071.022 (MainTransfer.lean:675–695) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with `Langlands.NYLL`, use focused
imports and expand the extension-subgroup abbreviation to its exact Mathlib body.
See the paired Markdown for the full correspondence and all modifications, and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory CyclicCohomology
open scoped BigOperators

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The element of `A_L` obtained by summing the conjugates indexed by a
right transversal for `G(L/K')` in `G(L/K)`.  Its `L | K'` norm is the
`L | K` norm of the original element. -/
noncomputable def transferNormNaturalityNormWitness
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : ((L.toSubgroup.subgroupOf K.toSubgroup)).Normal]
    [hL'normal : ((L.toSubgroup.subgroupOf K'.toSubgroup)).Normal]
    [Finite (K.toSubgroup ⧸
      (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A L) :
    ambientFixedAddSubgroup A L := by
  let H := transferNormNaturalityIntermediateSubgroup K K' L hLK' hK'K
  let T := PortInternal.M071.d017 K K' L hLK' hK'K
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : Fintype (T : Set (K.toSubgroup ⧸
      (L.toSubgroup.subgroupOf K.toSubgroup))) :=
    T.2.finite_right.fintype
  let E := extensionFixedRepresentation A K L
    (hLK'.trans hK'K) hLnormal
  let eA := extensionFixedRepresentationEquiv A K L
    (hLK'.trans hK'K) hLnormal
  exact eA (∑ t : (T : Set _), E.ρ t.1 (eA.symm a))


end
end Langlands.NYLL.ClassFormation
