/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.OrderStatements

/-!
# NYLL M296.015: the order and reverse subgroup containment

Modified by Worker 261, 14 November 2026: extract `le_iff` (M296.015,
source lines 157–160) from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, and express the conclusion using the published
`le_iffStatement`. The complete source telescope and proof `Iff.rfl` are
preserved. The paired Markdown records the modifications and proof.
See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The order on finite abelian subextensions is characterized by containment of their fields. -/
theorem le_iff (L₁ L₂ : FiniteAbelianSubextension K) :
    le_iffStatement L₁ L₂ :=
  Iff.rfl

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
