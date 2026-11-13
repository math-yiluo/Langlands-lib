/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only M086.019 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and keep the docstring, binders and body. Replace the source imports
by the published modules defining extensionSubgroup and
finiteReciprocityNaturalityRestriction, and open only the namespace of
extensionSubgroup. The section variables of the source are shadowed by the
definition's own binders and are not included, so they are omitted. Omit
all other declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.GroupTheory.Abelianization.Defs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.Restriction.Definitions

/-!
# Abelianized restriction in the norm/restriction naturality diagram

Restriction between finite Galois quotients of abstract field extensions,
after applying abelianization.
-/

namespace Langlands.NYLL.ClassFormation

open Langlands.NYLL.CyclicCohomology

noncomputable section

/-- Restriction in the first diagram of reciprocity naturality, after applying
abelianization. -/
def normResidueNaturalityAbelianizedRestriction
    {G : Type*} [Group G] [TopologicalSpace G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [hL'normal : (extensionSubgroup K' L' hL'K').Normal] :
    Abelianization
        (K'.toSubgroup ⧸ extensionSubgroup K' L' hL'K') →*
      Abelianization (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
  Abelianization.map
    (finiteReciprocityNaturalityRestriction K K' L L' hLK hL'K' hK'K hL'L)

end

end Langlands.NYLL.ClassFormation
