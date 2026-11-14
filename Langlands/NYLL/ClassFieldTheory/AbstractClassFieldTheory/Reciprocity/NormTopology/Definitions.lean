/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# NYLL M295.001: the norm subgroup of a finite Galois subextension

Modified by Worker 507: extract only source lines 39–43 of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/NormTopology.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the source
namespace by `Langlands.NYLL`, and replace the source imports by focused
Library imports. The construction and its complete telescope are unchanged.
The paired Markdown records the source correspondence and modifications.
See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The actual norm subgroup belonging to a packaged finite Galois
extension. -/
def normSubgroup (A : Rep ℤ G) (L : FiniteGaloisSubextension K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI := L.finite
  exact finiteNormSubgroup A K L.field L.below

end FiniteGaloisSubextension

end Langlands.NYLL.ClassFormation

end
