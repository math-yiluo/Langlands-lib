/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 147, 13 November 2026:
Extract the proof of M132.062 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 818–832. Add the Langlands.NYLL
namespace prefix. Keep the protected theorem name and the source telescope, and give
the theorem the published target applied to its parameters as its type; the original
proof is followed unchanged, its first `change` also unfolding the target.
Import only QuotientAlgebraStatements. Omit the source noncomputable section and
all other source declarations. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements

/-!
# Induction on classes of `𝓂^n/𝓂^(n+1)`

A property of classes in the ideal-power quotient holds for every class once it
holds for the class of every element of `𝓂^n`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Eliminate an ideal-power quotient class through its canonical class map. -/
protected theorem MaximalIdealPowSuccQuot.inductionOn
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n → Prop}
    (q : MaximalIdealPowSuccQuot K n)
    (h : ∀ a : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)) :
    MaximalIdealPowSuccQuot.inductionOnStatement n (motive := motive) q h := by
  change motive
    (show ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u) ⧸
      maximalIdealPowSuccSubmodule K n from q)
  refine Quotient.inductionOn q ?_
  intro a
  exact h a

end Langlands.NYLL.LocalFieldTheory
