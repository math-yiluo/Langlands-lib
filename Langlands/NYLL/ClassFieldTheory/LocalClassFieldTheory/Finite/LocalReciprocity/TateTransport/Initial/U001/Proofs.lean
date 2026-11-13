/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 13 November 2026 UTC:
Extract only the proof of M100.001 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TateTransport.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published TateTransport Initial
Statements module. Omit the unused namespace openings, noncomputable section
and section name, keep the source section variables, and state the theorem
as the published Statement applied to the source parameters. The proof is
unchanged. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport.Initial.Statements

/-!
# Cyclic generators under group isomorphisms

The proof that the image of a generator of a group under a group isomorphism
generates the target group.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

variable {Q P : Type} [Group Q] [Group P]

/-- A generator remains a generator after applying a group isomorphism. -/
theorem map_cyclicGenerator (e : Q ≃* P) (g : Q)
    (hg : ∀ q : Q, q ∈ Subgroup.zpowers g) :
    map_cyclicGeneratorStatement e g hg := by
  intro p
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (e.symm p))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  rw [← map_zpow e, hn, e.apply_symm_apply]

end Langlands.NYLL.LocalClassFieldTheory
