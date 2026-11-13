/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 147, 13 November 2026:
Extract the proof of M132.063 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709, lines 832–848. Add the Langlands.NYLL
namespace prefix. Because the submission schema accepts only ASCII declaration
names, the submitted theorem is named `inductionOn2` and has the published ASCII
wrapper target `inductionOn2Statement` applied to its parameters as its type; a
leading `show` unfolds that target to the source conclusion `motive q r`. The
source proof, which applies the published M132.062 theorem
`MaximalIdealPowSuccQuot.inductionOn` first to `q` and then to `r`, is kept
verbatim. The source-named theorem `inductionOn₂`, typed by the published
`inductionOn₂Statement`, is kept as a one-line consequence of `inductionOn2`.
Import only the wrapper statement module and the M132.062 proof module. Omit the
source noncomputable section and all other source declarations. The original
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.InductionOn2Statement
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U062.Proofs

/-!
# Binary induction on classes of `𝓂^n/𝓂^(n+1)`

A two-variable property of classes in the ideal-power quotient holds for every pair
of classes once it holds for the classes of every pair of elements of `𝓂^n`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Binary elimination through arbitrary ideal-power representatives. -/
protected theorem MaximalIdealPowSuccQuot.inductionOn2
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n →
      MaximalIdealPowSuccQuot K n → Prop}
    (q r : MaximalIdealPowSuccQuot K n)
    (h : ∀ a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)
        (maximalIdealPowSuccQuotMk K n b)) :
    MaximalIdealPowSuccQuot.inductionOn2Statement n (motive := motive) q r h := by
  show motive q r
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun q' => motive q' r) q ?_
  intro a
  refine MaximalIdealPowSuccQuot.inductionOn n
    (motive := fun r' => motive (maximalIdealPowSuccQuotMk K n a) r') r ?_
  intro b
  exact h a b

/-- Binary elimination under the source name, with the published
`inductionOn₂Statement` as its type. -/
protected theorem MaximalIdealPowSuccQuot.inductionOn₂
    {K : Type u} [Field K] [ValuativeRel K] (n : Nat)
    {motive : MaximalIdealPowSuccQuot K n →
      MaximalIdealPowSuccQuot K n → Prop}
    (q r : MaximalIdealPowSuccQuot K n)
    (h : ∀ a b : ((𝓂[K] ^ n : Ideal 𝒪[K]) : Type u),
      motive (maximalIdealPowSuccQuotMk K n a)
        (maximalIdealPowSuccQuotMk K n b)) :
    MaximalIdealPowSuccQuot.inductionOn₂Statement n (motive := motive) q r h :=
  MaximalIdealPowSuccQuot.inductionOn2 n (motive := motive) q r h

end Langlands.NYLL.LocalFieldTheory
