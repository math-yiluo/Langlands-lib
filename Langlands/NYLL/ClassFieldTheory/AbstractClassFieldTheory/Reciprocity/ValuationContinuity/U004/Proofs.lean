/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 114 (2026-11-15): extract only the proof of M301.004 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean
(lines 57–70, section context lines 22–36) at commit
fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL; import only the
published Statements module of
Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity
and state the theorem as that module's
`unramifiedDegreeKernelWithin_isClosedStatement` applied to the source binders,
opening it with `unfold` before the unchanged source tactic proof. The
noncomputable section, the scoped Topology open and the unused source opens
are omitted. Retained license and notices: licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.Statements

/-!
# Closedness of the reduction-modulo-`f` kernel of `d_K` (NYLL M301.004)

The kernel of the normalized degree reduced modulo a positive integer `f` is
closed in the subspace topology of the finite-residue field subgroup.
-/

namespace Langlands.NYLL.ClassFormation

universe u

section DegreeOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/--
The kernel of normalized degree modulo a positive integer is closed inside the finite-residue
field subgroup.
-/
theorem unramifiedDegreeKernelWithin_isClosed (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    unramifiedDegreeKernelWithin_isClosedStatement D K f hf := by
  unfold unramifiedDegreeKernelWithin_isClosedStatement
  change IsClosed
    ((unramifiedDegreeHom D K f hf) ⁻¹' ({1} :
      Set (Multiplicative (ZMod f))))
  exact isClosed_singleton.preimage
    (unramifiedDegreeHom D K f hf).continuous_toFun

end DegreeData

end DegreeOnly

end Langlands.NYLL.ClassFormation
