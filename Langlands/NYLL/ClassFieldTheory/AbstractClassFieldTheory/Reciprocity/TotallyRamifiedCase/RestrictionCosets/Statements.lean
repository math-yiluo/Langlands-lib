/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# Targets: equal restrictions in finite Galois towers

Modified by Worker 5264, 15 November 2026: state the source theorems M080.008
`FiniteGaloisSubextension.commute_of_same_restriction_of_inertia_le` and
M080.009 `FiniteGaloisSubextension.relativeCosetAction_eq_of_restriction_eq`
of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, replace the source import by focused published imports, omit
the proofs and the rest of the source file, and turn off the unused-variable
linter for the binders `hEnormal`, `hIE` and `hres`, which the propositions
do not mention. See
the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

set_option linter.unusedVariables false in
/-- Target: two auxiliary quotient elements commute when they have the same
restriction and the auxiliary field contains the inertia subgroup. -/
def commute_of_same_restriction_of_inertia_leStatement
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    (hIE : (D.fieldInertia E.field).toSubgroup ≤ M.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (g t : E.base.toSubgroup ⧸
      extensionSubgroup E.base M.field M.below)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) : Prop :=
    Commute g t

set_option linter.unusedVariables false in
/-- Target: equal restrictions induce equal relative coset actions on
elements fixed by the upper field. -/
def relativeCosetAction_eq_of_restriction_eqStatement
    (A : Rep ℤ G) (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (a : ambientFixedAddSubgroup A E.field)
    (g t : E.base.toSubgroup ⧸
      extensionSubgroup E.base M.field M.below)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) : Prop :=
    relativeCosetAction A E.base M.field M.below
        (fixedFieldInclusion A E.field M.field hME a) g =
      relativeCosetAction A E.base M.field M.below
        (fixedFieldInclusion A E.field M.field hME a) t

end FiniteGaloisSubextension

end Langlands.NYLL.ClassFormation
