/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.U010.Definitions

/-!
# NYLL M020: the closed cyclic-factor subgroup lies below the base

Modified by Worker 4918: state the source theorem M020.011
`closedCyclicFactorSubgroup_le_base` of the pinned NYLL
`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean` as a
Prop-valued definition ending in `Statement`, with the source binders and
statement, under the namespace prefix `Langlands.NYLL`. The proof is
omitted. The source's module import is replaced by the module of the
published M020.010 `closedCyclicFactorSubgroup`. The paired Markdown records
every modification. See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.KummerTheory

open CyclicCohomology

noncomputable section

section ClosedCyclicSubextensions

variable {G : Type*} [Group G] [TopologicalSpace G]

variable [IsTopologicalGroup G]

/-- Target M020.011: the cyclic-factor intermediate subgroup lies below the
base subgroup `G_K`. -/
def closedCyclicFactorSubgroup_le_baseStatement
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) : Prop :=
  (closedCyclicFactorSubgroup K L hLK f).toSubgroup ≤ K.toSubgroup

end ClosedCyclicSubextensions

end

end Langlands.NYLL.KummerTheory
