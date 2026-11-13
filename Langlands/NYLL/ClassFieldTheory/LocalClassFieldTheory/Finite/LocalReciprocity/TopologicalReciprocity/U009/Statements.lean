/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Algebra.Group.TopologicalAbelianization

/-!
# Discrete commutator closure target

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section
namespace Langlands.NYLL.PortInternal.M257
def d009Statement
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] : Prop :=
Subgroup.topologicalClosure (commutator G) = commutator G

end Langlands.NYLL.PortInternal.M257
