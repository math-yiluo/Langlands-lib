/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Closed fixing subgroups

This module packages the closed subgroup attached to an intermediate field in
the Krull topology.

Adapted from NYLL `Nyll/ValuedFieldTheory/Ramification/GaloisValuation/ClosedFixingSubgroup.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709, lines 23–29 (M087.001).
Worker 5181 prefixed the namespace by `Langlands.NYLL` and moved the module into
the `ClosedFixingSubgroup/Definitions` file. The original imports, the
`noncomputable section`, the attribute, the binders, the universes and the body
are unchanged. The original license and notices are retained in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.RamificationTheory

/-- The closed fixing subgroup attached to an intermediate field. -/
@[implicit_reducible]
noncomputable def closedFixingSubgroup
    (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) : ClosedSubgroup Gal(Ω/k) :=
  ⟨K.fixingSubgroup, InfiniteGalois.fixingSubgroup_isClosed K⟩

end Langlands.NYLL.RamificationTheory
