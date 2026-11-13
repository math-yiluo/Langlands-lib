/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Adapted by Worker 5264 from pinned NYLL PrincipalUnitQuotients.lean.
-- ASCII-named wrapper of the published M132.063 target; see the paired Markdown.

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.QuotientAlgebraStatements

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Exact source target M132.063 (binary elimination through arbitrary ideal-power
representatives) under the ASCII name `inductionOn2Statement`: it applies the
published `MaximalIdealPowSuccQuot.inductionOn₂Statement` to the same arguments. -/
protected def MaximalIdealPowSuccQuot.inductionOn2Statement
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n →
      MaximalIdealPowSuccQuot K n → Prop}
    (q r : MaximalIdealPowSuccQuot K n)
    (h : ∀ a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)
        (maximalIdealPowSuccQuotMk K n b)) : Prop :=
  MaximalIdealPowSuccQuot.inductionOn₂Statement (motive := motive) n q r h

end

end Langlands.NYLL.LocalFieldTheory
