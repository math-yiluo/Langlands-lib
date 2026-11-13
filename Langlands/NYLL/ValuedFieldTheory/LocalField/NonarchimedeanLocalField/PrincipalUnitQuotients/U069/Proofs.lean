/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 147, 13 November 2026:
Extract the proof of M132.069 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 919–932. Add the Langlands.NYLL
namespace prefix. Keep the source telescope and give the theorem the published
target applied to its parameters as its type; the original proof is followed
unchanged, its first `change` also unfolding the target.
Import only QuotientAlgebraStatements. Omit the source noncomputable section and
all other source declarations. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements

/-!
# The zero class of `𝓂^n/𝓂^(n+1)`

The class of an element of `𝓂^n` vanishes exactly when the element lies in
`𝓂^(n+1)`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The class of an element of `𝓂^n` is zero exactly when its value lies in `𝓂^(n+1)`. -/
theorem maximalIdealPowSuccQuotMk_eq_zero_iff
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat)
    (a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u)) :
    maximalIdealPowSuccQuotMk_eq_zero_iffStatement K n a := by
  change (Submodule.Quotient.mk a :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

end Langlands.NYLL.LocalFieldTheory
