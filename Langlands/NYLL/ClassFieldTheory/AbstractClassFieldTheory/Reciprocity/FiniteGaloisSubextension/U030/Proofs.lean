/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Statements

/-!
# NYLL M040.030: the left compositum bound

Modified by Worker 242: extract the source theorem from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`,
prefix its namespace with `Langlands.NYLL`, replace the source import with the
published target module, and express its type as that target. The source proof
is retained. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation.FiniteGaloisSubextension

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {K : ClosedSubgroup G}

/-- The constructed Galois compositum satisfies the left comparison bound. -/
theorem compositum_le_left (L₁ L₂ : FiniteGaloisSubextension K) :
    compositum_le_leftStatement L₁ L₂ :=
  inf_le_left

end Langlands.NYLL.ClassFormation.FiniteGaloisSubextension
