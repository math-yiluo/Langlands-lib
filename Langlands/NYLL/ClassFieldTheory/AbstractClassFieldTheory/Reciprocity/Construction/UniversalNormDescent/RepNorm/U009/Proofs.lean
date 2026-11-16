/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 747 (2026-11-16): extract this focused M043.009 proof
from the pinned source at fbd320cd8b1b06487c58227e92eb135794267709;
prefix its namespace by Langlands.NYLL, import its published Prop target,
and prove that exact target. Proof adaptations and dependencies are recorded
in the paired Markdown. Retained license and notices:
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.RepNorm.Statements

namespace Langlands.NYLL.ClassFormation

noncomputable section

open CategoryTheory
open scoped BigOperators

/-- Proof of NYLL M043.009, with the exact published target: the norm of a
finite cyclic representation is the sum of the actions of the first `n`
powers of a generator, where `n` is the group order. -/
theorem rep_norm_eq_generatorPowerSum
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n) (x : B.V) :
    rep_norm_eq_generatorPowerSumStatement B g hg n hcard x := by
  unfold rep_norm_eq_generatorPowerSumStatement
  classical
  have horder : orderOf g = n := by
    calc
      orderOf g = Nat.card Q :=
        orderOf_eq_card_of_forall_mem_zpowers hg
      _ = Fintype.card Q := Nat.card_eq_fintype_card
      _ = n := hcard
  let e : Fin n ≃ Q := Equiv.ofBijective (fun i => g ^ i.1) (by
    constructor
    · intro i j hij
      apply Fin.ext
      have hmod : i.1 ≡ j.1 [MOD orderOf g] :=
        (pow_eq_pow_iff_modEq).mp hij
      rw [horder] at hmod
      exact hmod.eq_of_lt_of_lt i.2 j.2
    · intro q
      have himage :
          Finset.image (fun i => g ^ i) (Finset.range n) = Finset.univ := by
        rw [← horder]
        exact IsCyclic.image_range_orderOf hg
      have hq : q ∈ Finset.image (fun i => g ^ i) (Finset.range n) := by
        rw [himage]
        exact Finset.mem_univ q
      obtain ⟨i, hi, hiq⟩ := Finset.mem_image.mp hq
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, hiq⟩)
  have hsum : (∑ q : Q, B.ρ q x) =
      ∑ i : Fin n, B.ρ (g ^ i.1) x :=
    (e.sum_comp (fun q : Q => B.ρ q x)).symm
  simpa [Rep.norm, Representation.norm] using hsum

end

end Langlands.NYLL.ClassFormation
