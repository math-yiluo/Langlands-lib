/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# Restriction between named finite Galois quotients

Modified by Worker 5264, 15 November 2026: extract the definition M080.001
`FiniteGaloisSubextension.bundledRestrictionHom` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source import by focused published imports,
and omit the rest of the source file and the unused `open KummerTheory` and
`open CyclicCohomology`. The binders, docstring and body are unchanged. See
the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- Restriction between the named finite Galois quotient boundaries. -/
def bundledRestrictionHom
    {K : ClosedSubgroup G}
    (M L : FiniteGaloisSubextension K)
    (hML : M.field.toSubgroup ≤ L.field.toSubgroup) :
    M.extensionQuotient →* L.extensionQuotient :=
  L.extensionQuotientMulEquiv.symm.toMonoidHom.comp
    ((abstractReciprocityRestriction
      K L.field M.field hML L.below).comp
        M.extensionQuotientMulEquiv.toMonoidHom)

end FiniteGaloisSubextension

end Langlands.NYLL.ClassFormation
