/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 15 November 2026 UTC:
Extract only the proof of M020.008 (extensionSubgroup_isClosed) from
Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean
(lines 133–142) at fbd320cd8b1b06487c58227e92eb135794267709. Add the
Langlands.NYLL namespace prefix and import only the published
KummerAbelianCyclicFactors Statements module. Keep the section name, the
section variable line, the noncomputable section, the docstring, the binders
and the tactic proof, and state the theorem as the published Statement
applied to the source parameters. Open Langlands.NYLL.CyclicCohomology for
extensionSubgroup. Omit the other declarations of the source file. The
original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.Statements

/-!
# Closedness of `G_L` inside `G_K`

If `L ≤ K` are closed subgroups of a topological group `G`, then `L`, viewed
as a subgroup of `K` with the subspace topology, is closed: it is the preimage
of the closed set `L` under the continuous inclusion `K → G`.
-/

namespace Langlands.NYLL.KummerTheory

open Langlands.NYLL.CyclicCohomology

noncomputable section

section ClosedCyclicSubextensions

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A closed abstract field subgroup `G_L` remains closed when regarded as
a subgroup of the larger abstract field subgroup `G_K`. -/
theorem extensionSubgroup_isClosed
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) :
    extensionSubgroup_isClosedStatement K L hLK := by
  change IsClosed ((fun x : K.toSubgroup => (x : G)) ⁻¹' (L : Set G))
  exact L.isClosed'.preimage continuous_subtype_val

end ClosedCyclicSubextensions

end

end Langlands.NYLL.KummerTheory
