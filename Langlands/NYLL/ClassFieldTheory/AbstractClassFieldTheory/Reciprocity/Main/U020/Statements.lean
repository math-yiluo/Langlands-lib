/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the asserted type of M086.020
normResidueNaturalityAbelianizedRestriction_of_mk from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Main.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and package all binders of the theorem, in order and with the same
binder kinds and the universe of `Type*`, inside a closed Prop-valued
definition with the suffix Statement; the two instance hypotheses, which the
conclusion does not name, become anonymous. Write extensionSubgroup by its full
name, replace the source imports by the published M086.019 module, defer
the truth proof and install no simp registration. Omit all other
declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main.U019.Definitions

/-!
# Abelianized restriction on quotient representatives: statement
-/

namespace Langlands.NYLL.ClassFormation

universe u

/-- Establishes the identity `normResidueNaturalityAbelianizedRestriction K K' L L' hLK hL'K' hK'K
hL'L (Abelianization.of (QuotientGroup.mk k')) = Abelianization.of (QuotientGroup.mk
(Subgroup.inclusion hK'K k'))`. -/
def normResidueNaturalityAbelianizedRestriction_of_mkStatement : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G]
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [(Langlands.NYLL.CyclicCohomology.extensionSubgroup K L hLK).Normal]
    [(Langlands.NYLL.CyclicCohomology.extensionSubgroup K' L' hL'K').Normal]
    (k' : K'.toSubgroup),
    normResidueNaturalityAbelianizedRestriction K K' L L'
        hLK hL'K' hK'K hL'L
        (Abelianization.of (QuotientGroup.mk k')) =
      Abelianization.of
        (QuotientGroup.mk (Subgroup.inclusion hK'K k'))

end Langlands.NYLL.ClassFormation
