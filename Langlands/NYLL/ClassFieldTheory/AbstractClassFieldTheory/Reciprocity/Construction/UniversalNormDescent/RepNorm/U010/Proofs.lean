/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 747 (2026-11-16): extract this focused M043.010 proof
from the pinned source at fbd320cd8b1b06487c58227e92eb135794267709;
prefix its namespace by Langlands.NYLL, import its published Prop target,
and prove that exact target. Proof adaptations and dependencies are recorded
in the paired Markdown. Retained license and notices:
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.Statements

namespace Langlands.NYLL.ClassFormation

noncomputable section

open CategoryTheory
open scoped BigOperators

/-- Proof of NYLL M043.010, with the exact published target: powers in a
representation are the iterates of the corresponding action map. -/
theorem rep_action_pow_eq_iterate {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (n : ℕ) (x : B.V) :
    rep_action_pow_eq_iterateStatement B g n x := by
  unfold rep_action_pow_eq_iterateStatement
  let : Module ℤ B.V := B.hV2
  rw [map_pow, Module.End.coe_pow]

end

end Langlands.NYLL.ClassFormation
