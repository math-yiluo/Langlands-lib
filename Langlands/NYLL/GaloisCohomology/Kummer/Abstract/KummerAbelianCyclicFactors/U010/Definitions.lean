/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U009.Proofs

/-!
# NYLL M020: the closed cyclic-factor intermediate subgroup

Modified by Worker 4918: extract M020.010 `closedCyclicFactorSubgroup` from
the pinned NYLL
`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean` and
prefix the namespace with `Langlands.NYLL`. The source's module import is
replaced by the module of the published proof of M020.009
`cyclicFactorSubgroup_isClosed`, which the closedness field uses. The
definition, its binders and its body are otherwise unchanged. The paired
Markdown records every modification. See `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.KummerTheory

open CyclicCohomology

noncomputable section

section ClosedCyclicSubextensions

variable {G : Type*} [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G]

/-- The closed abstract intermediate field attached to one cyclic coordinate
factor of `G_K/G_L`. -/
def closedCyclicFactorSubgroup
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) :
    ClosedSubgroup G where
  toSubgroup :=
    (cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f).map
      K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      ((fun x : K.toSubgroup => (x : G)) ''
        (cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f :
          Set K.toSubgroup))
    exact K.isClosed'.isClosedMap_subtype_val _
      (cyclicFactorSubgroup_isClosed K L hLK f)

end ClosedCyclicSubextensions

end

end Langlands.NYLL.KummerTheory
