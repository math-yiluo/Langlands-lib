/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 384 (2026-10-30): extract M105.013 and its small
M105.011/.012 supporting arguments from AdicPower.lean at upstream commit
fbd320cd8b1b06487c58227e92eb135794267709. Import the unchanged published
statement, prefix the namespace with Langlands.NYLL, and prove the exact
closed proposition with independent ring/module universes. Inline the
Hausdorff and precomplete helpers as local proofs, preserving the supplied
module action and the positive-exponent subsequence argument. Replace the
source import by the published statement module; omit unrelated source
declarations and global instances. Retained license/notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.MaximalIdealCompletenessStatements

/-!
# Completeness from a positive power of an ideal

NYLL M105.013: completeness for `I ^ n`, with `0 < n`, implies completeness
for `I` on the same module. Separation and precompleteness are obtained
using the subsequence of indices `n * k`.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

/-- Completeness for a positive power implies completeness for the ideal,
with exactly the quantifiers of the published closed proposition. -/
theorem isAdicComplete_of_isAdicComplete_pow.{u, v} :
    IsAdicCompleteOfIsAdicCompletePowStatement.{u, v} := by
  intro R M _ _ _ I n hn _
  have hhaus : IsHausdorff I M := by
    refine ⟨fun x hx => IsHausdorff.haus
      (inferInstance : IsHausdorff (I ^ n) M) x ?_⟩
    intro k
    simpa [pow_mul] using hx (n * k)
  have hprec : IsPrecomplete I M := by
    refine ⟨fun f hf => ?_⟩
    have hsub :
        ∀ {a b : ℕ}, a ≤ b →
          f (n * a) ≡ f (n * b)
            [SMOD ((I ^ n) ^ a • ⊤ : Submodule R M)] := by
      intro a b hab
      have hle : n * a ≤ n * b := Nat.mul_le_mul_left n hab
      simpa [pow_mul] using hf hle
    obtain ⟨L, hL⟩ :=
      IsPrecomplete.prec (I := I ^ n) (M := M)
        (inferInstance : IsPrecomplete (I ^ n) M)
        (f := fun k => f (n * k)) hsub
    refine ⟨L, fun m => ?_⟩
    have hm : m ≤ n * m := by
      simpa using Nat.mul_le_mul_right m (Nat.succ_le_of_lt hn)
    have hfm : f m ≡ f (n * m)
        [SMOD (I ^ m • ⊤ : Submodule R M)] :=
      hf hm
    have htail : f (n * m) ≡ L
        [SMOD (I ^ m • ⊤ : Submodule R M)] := by
      apply SModEq.mono (Submodule.pow_smul_top_le I M hm)
      simpa [pow_mul] using hL m
    exact hfm.trans htail
  exact { toIsHausdorff := hhaus, toIsPrecomplete := hprec }

end Langlands.NYLL.ValuationTheory.DiscreteValuationField
