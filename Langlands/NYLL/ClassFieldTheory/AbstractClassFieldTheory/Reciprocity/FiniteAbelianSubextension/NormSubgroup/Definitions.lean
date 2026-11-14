/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions

/-!
# NYLL M296: the norm subgroup of a finite abelian subextension

Modified by Worker 449, 14 November 2026: extract the data definition M296.030
(source lines 404–419, with the section scaffolding of lines 30–34) from the
pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, replace the source imports by the published finite abelian
data module and the published `finiteNormSubgroup` module, and drop the unused
`universe u`. The declaration, binders, docstring and body are otherwise
unchanged. The paired Markdown records every modification. See
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology KummerTheory

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The norm subgroup assigned to a finite abelian extension,
`N_L = N_{L/K} A_L` in the finite abelian class-field classification. -/
def normSubgroup (A : Rep ℤ G) (L : FiniteAbelianSubextension K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI : Finite (K.toSubgroup ⧸
      extensionSubgroup K L.field L.below) := L.finite
  exact finiteNormSubgroup A K L.field L.below

end FiniteAbelianSubextension

end Representation

end Langlands.NYLL.ClassFormation
