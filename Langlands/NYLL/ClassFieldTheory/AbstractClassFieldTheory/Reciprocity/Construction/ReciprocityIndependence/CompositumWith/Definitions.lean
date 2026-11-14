/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.Definitions

/-!
# NYLL M033.008: the compositum of a finite intermediate field with a field

Modified by Worker 483: extract M033.008 from the pinned NYLL
ReciprocityIndependence.lean, prefix the namespace with Langlands.NYLL and
use the focused M029 import. The declaration, its binders, universe and body
are otherwise unchanged. See the paired Markdown and licenses/NYLL/LICENSE
and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

section groupTheoreticRefinements

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- The field compositum `MΣ`, contravariantly represented by
`G_M ∩ G_Σ`. -/
def compositumWith
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) : ClosedSubgroup G :=
  M.field ⊓ S

end FiniteIntermediateField

end groupTheoreticRefinements

end
end Langlands.NYLL.ClassFormation
