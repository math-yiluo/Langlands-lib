/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 147, 13 November 2026:
Extract the proof of M132.086 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 1161–1173. Add the Langlands.NYLL
namespace prefix. Keep the source telescope and give the theorem the published
target applied to its parameters as its type; a leading `show` unfolds that target
to the source conclusion, after which the original proof is followed unchanged.
Import only QuotientAlgebraStatements. Omit the source noncomputable section and
all other source declarations. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements

/-!
# Products of two elements of a positive maximal-ideal power

For `n ≥ 1`, the product of two elements of `𝓂^n` lies in `𝓂^(n+1)`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Products of two elements of `𝓂^n`, for `n ≥ 1`, lie in `𝓂^(n+1)`. -/
theorem maximalIdealPow_mul_mem_succ
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n)
    (a b : (𝓂[K] ^ n : Ideal 𝒪[K])) :
    maximalIdealPow_mul_mem_succStatement K hn a b := by
  show ((a : 𝒪[K]) * (b : 𝒪[K])) ∈ (𝓂[K] ^ (n + 1) : Ideal 𝒪[K])
  have hmul : ((a : 𝒪[K]) * (b : 𝒪[K])) ∈ (𝓂[K] ^ (n + n) : Ideal 𝒪[K]) := by
    simpa [pow_add] using (Ideal.mul_mem_mul a.2 b.2)
  have hle : (𝓂[K] ^ (n + n) : Ideal 𝒪[K]) ≤
      (𝓂[K] ^ (n + 1) : Ideal 𝒪[K]) :=
    Ideal.pow_le_pow_right (Nat.add_le_add_left hn n)
  exact hle hmul

end Langlands.NYLL.LocalFieldTheory
