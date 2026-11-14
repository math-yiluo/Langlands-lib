/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements

/-!
# NYLL M026.002: membership in a conjugate closed subgroup

Modified by Worker 5014, 14 November 2026: extract the theorem
`conjugateClosedSubgroup_mem` (M026.002) from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 into this focused module, prefix its
namespace with `Langlands.NYLL`, replace the source imports by the published
statement module, state its type through the published
`conjugateClosedSubgroup_memStatement`, and omit the source `@[simp]`
attribute (the type is now the Prop-valued target). The source tactic proof
is retained unchanged. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open scoped Pointwise

/--
Characterizes `x ∈ conjugateClosedSubgroup K σ` by the equivalent condition `σ * x * σ⁻¹ ∈ K`.
-/
theorem conjugateClosedSubgroup_mem {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G]
    (K : ClosedSubgroup G) (σ x : G) :
    conjugateClosedSubgroup_memStatement K σ x := by
  change x ∈ (ConjAct.toConjAct σ⁻¹ • K.toSubgroup : Subgroup G) ↔
    σ * x * σ⁻¹ ∈ K.toSubgroup
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]

end Langlands.NYLL.ClassFormation
