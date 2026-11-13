/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U012.Statements
import Langlands.NYLL.GaloisCohomology.GroupTheory.QuotientTower

/-!
# Multiplication of cardinal relative indices

Modified by Worker 183: extract the proof of NYLL M006.014, prefix its
namespace with Langlands.NYLL, state its type using the published target,
and reuse the published quotient-tower equivalence. The source proof route,
universe, binder order and hypotheses are preserved.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

universe u

variable {G : Type u} [Group G]

/-- Relative cardinal indices multiply in every subgroup tower. -/
theorem relativeIndexCardinal_mul {M L K : Subgroup G}
    (hML : M ≤ L) (hLK : L ≤ K) :
    relativeIndexCardinal_mulStatement hML hLK := by
  unfold relativeIndexCardinal_mulStatement
  rw [mul_comm, relativeIndexCardinal, relativeIndexCardinal,
    relativeIndexCardinal, intersectionIndexCardinal, intersectionIndexCardinal,
    intersectionIndexCardinal, Cardinal.mul_def]
  exact Cardinal.mk_congr
    (Langlands.NYLL.Subgroup.quotientTowerEquiv hML hLK).symm

end Langlands.NYLL.ClassFormation
