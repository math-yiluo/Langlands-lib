/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 13 November 2026 UTC:
Extract only the proof of M257.009 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean
at fbd320cd8b1b06487c58227e92eb135794267709. The source declaration is the
private theorem commutator_topologicalClosure_eq in LocalClassFieldTheory;
following the published statement it becomes the public theorem
Langlands.NYLL.PortInternal.M257.d009. Import only the published
TopologicalReciprocity U009 Statements module, omit the unused section
variables, namespace openings and local instances, and state the theorem as
the published Statement applied to the source parameters. The proof is
unchanged. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U009.Statements

/-!
# Closure of the commutator subgroup of a discrete group

The proof that in a discrete topological group the commutator subgroup equals
its topological closure.
-/

namespace Langlands.NYLL.PortInternal.M257

/-- In a discrete topological group the commutator subgroup is closed, so it
equals its topological closure. -/
theorem d009
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] :
    d009Statement G := by
  apply le_antisymm
  · exact Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_discrete _)
  · exact Subgroup.le_topologicalClosure _

end Langlands.NYLL.PortInternal.M257
