/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.UnramifiedExtension.Statements

/-!
# NYLL M301.006–.007: membership and inclusion of the unramified subgroup

Modified by Worker 499: extract the two proofs from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`,
prefix the namespace with `Langlands.NYLL`, import the published targets,
and express each theorem's type by its corresponding Statement definition.
Keep the source universe, complete telescopes, proof terms and membership
theorem's `@[simp]` attribute. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

open scoped Topology

namespace Langlands.NYLL.ClassFormation

universe u

section DegreeOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Membership in the unramified subgroup is membership in the image of its kernel. -/
@[simp]
theorem mem_unramifiedExtensionOfDegree_iff (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) (g : G) :
    mem_unramifiedExtensionOfDegree_iffStatement D K f hf g :=
  Iff.rfl

/-- The degree-`f` unramified subgroup is contained in the field subgroup. -/
theorem unramifiedExtensionOfDegree_le (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    unramifiedExtensionOfDegree_leStatement D K f hf := by
  rintro g ⟨k, _, rfl⟩
  exact k.2

end DegreeData

end DegreeOnly

end Langlands.NYLL.ClassFormation
