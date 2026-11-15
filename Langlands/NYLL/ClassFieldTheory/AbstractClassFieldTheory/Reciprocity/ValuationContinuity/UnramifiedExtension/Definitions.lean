/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.U004.Proofs

/-!
# NYLL M301.005: the closed subgroup of the degree-`f` unramified extension

Modified by Worker 452: extract M301.005 `unramifiedExtensionOfDegree` from the
pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`,
prefix the namespace with `Langlands.NYLL`, and replace the source module
imports by the published proof of M301.004
`unramifiedDegreeKernelWithin_isClosed`, which the body uses. The universe,
variable declaration, docstring, telescope, result type and body are retained.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

open scoped Topology

namespace Langlands.NYLL.ClassFormation

universe u

section DegreeOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The actual fixed field of the reduction-modulo-`f` kernel of `d_K`. -/
def unramifiedExtensionOfDegree (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) : ClosedSubgroup G where
  toSubgroup :=
    (unramifiedDegreeKernelWithin D K f hf).map K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      (Subtype.val ''
        (unramifiedDegreeKernelWithin D K f hf : Set K.toSubgroup))
    exact K.field.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _
      (unramifiedDegreeKernelWithin_isClosed D K f hf)

end DegreeData

end DegreeOnly

end Langlands.NYLL.ClassFormation
