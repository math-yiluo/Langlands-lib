/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 313, 2026-11-13: isolate the cited proof from pinned commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with Langlands.NYLL,
and prove the exact closed proposition using focused imports. Changes to the
proof route are recorded in the paired Markdown.
Modified by Worker 287, 2026-11-14: reuse Worker 313's proof draft unchanged,
check it against the published target, and expand the paired proof documentation.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber.AdjoinStatement

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

theorem valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoin :
    valuationSubringAutOfUniqueExtension_sub_mem_of_mem_adjoinStatement.{u, v, w, x} := by
  intro K L _ _ _ base target _ huniq a z n sigma ha hz
  let e := valuationSubringAutOfUniqueExtension (base := base) (target := target) huniq sigma
  change e z - z ∈ target.maximalIdeal ^ n
  change e a - a ∈ target.maximalIdeal ^ n at ha
  induction hz using Algebra.adjoin_induction with
  | mem y hy =>
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact ha
  | algebraMap r =>
      have hcomm : e (algebraMap base.valuationSubring target.valuationSubring r) =
          algebraMap base.valuationSubring target.valuationSubring r := by
        apply Subtype.ext
        exact sigma.commutes (r : K)
      rw [hcomm, sub_self]
      exact Ideal.zero_mem _
  | add y z _ _ hy hz =>
      have hrewrite : e (y + z) - (y + z) = (e y - y) + (e z - z) := by
        rw [map_add]
        ring
      rw [hrewrite]
      exact Ideal.add_mem _ hy hz
  | mul y z _ _ hy hz =>
      have hrewrite : e (y * z) - y * z = e y * (e z - z) + (e y - y) * z := by
        rw [map_mul]
        ring
      rw [hrewrite]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hz) (Ideal.mul_mem_right _ _ hy)

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
