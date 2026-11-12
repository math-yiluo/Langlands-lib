/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5176, 10 November 2026:
Extract only the docstring and asserted type of M013.001 from
Nyll/GaloisCohomology/Topology/TotallyDisconnectedQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 21–27 of the theorem
at lines 21–97). Add the Langlands.NYLL namespace prefix and move all ten
original binders inside a closed Prop-valued definition, preserving their
order and binder kinds; the anonymous universe of the source's `Type*` is
named u. Both original imports are retained unchanged. Keep the source
hypothesis name hN and turn off only the unused-variables linter for this
declaration. Defer the truth proof (lines 28–97) and install no instance.
Replace the module docstring (lines 10–15) by a statement-only one and omit
M013.002–M013.004 (lines 101–187). The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Totally disconnected quotient groups: the M013.001 target

The closed assertion that the quotient of a compact Hausdorff totally
disconnected topological group by a closed normal subgroup, with the
quotient topology, is totally disconnected.
-/

namespace Langlands.NYLL.QuotientGroup

universe u

-- The source hypothesis name `hN` is kept although the proposition never mentions it.
set_option linter.unusedVariables false in
/-- A closed normal quotient of a compact Hausdorff totally disconnected
topological group is totally disconnected. -/
def totallyDisconnectedSpace_of_isClosedStatement : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)),
    TotallyDisconnectedSpace (G ⧸ N)

end Langlands.NYLL.QuotientGroup
