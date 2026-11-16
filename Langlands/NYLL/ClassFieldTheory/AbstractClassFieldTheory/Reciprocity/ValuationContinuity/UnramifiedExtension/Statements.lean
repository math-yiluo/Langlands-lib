/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.UnramifiedExtension.Definitions

/-!
# Targets for the closed subgroup of the degree-`f` unramified extension

Modified by Worker 452: extract the theorem signatures M301.006
`mem_unramifiedExtensionOfDegree_iff` and M301.007
`unramifiedExtensionOfDegree_le` from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`
as Prop-valued Statement definitions. Prefix the namespace with
`Langlands.NYLL`, append `Statement` to each name, keep the source universe,
variable declaration, parameters and binder kinds, omit the proofs and the
source `@[simp]` attribute of M301.006, and import only the published
M301.005 construction.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

open scoped Topology

namespace Langlands.NYLL.ClassFormation

universe u

section DegreeOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/--
Target: characterizes `g ∈ unramifiedExtensionOfDegree D K f hf` by the
equivalent condition `∃ k : K.toSubgroup, k ∈ unramifiedDegreeKernelWithin D K f hf ∧ k.1 = g`.
-/
def mem_unramifiedExtensionOfDegree_iffStatement (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) (g : G) : Prop :=
  g ∈ unramifiedExtensionOfDegree D K f hf ↔
    ∃ k : K.toSubgroup,
      k ∈ unramifiedDegreeKernelWithin D K f hf ∧ k.1 = g

/-- Target: the bound `(unramifiedExtensionOfDegree D K f hf).toSubgroup ≤ K.toSubgroup`. -/
def unramifiedExtensionOfDegree_leStatement (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) : Prop :=
  (unramifiedExtensionOfDegree D K f hf).toSubgroup ≤
    K.toSubgroup

end DegreeData

end DegreeOnly

end Langlands.NYLL.ClassFormation
