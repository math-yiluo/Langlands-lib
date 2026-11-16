/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 747 (2026-11-16): extract this focused M043.012 proof
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

/-- Local private copy of the M043.010 argument (the published theorem
`rep_action_pow_eq_iterate` is not yet in the Library at this workspace
base): powers act as iterates of the action map. -/
private theorem rep_action_pow_eq_iterate_local {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (n : ℕ) (x : B.V) :
    B.ρ (g ^ n) x = ((B.ρ g)^[n]) x := by
  let : Module ℤ B.V := B.hV2
  rw [map_pow, Module.End.coe_pow]

/-- Proof of NYLL M043.012, with the exact published target: every
nonnegative power fixes an element fixed by the original group element. -/
theorem rep_action_pow_fixed {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (x : B.V) (hx : B.ρ g x = x) (n : ℕ) :
    rep_action_pow_fixedStatement B g x hx n := by
  unfold rep_action_pow_fixedStatement
  rw [rep_action_pow_eq_iterate_local]
  exact Function.IsFixedPt.iterate hx n

end

end Langlands.NYLL.ClassFormation
