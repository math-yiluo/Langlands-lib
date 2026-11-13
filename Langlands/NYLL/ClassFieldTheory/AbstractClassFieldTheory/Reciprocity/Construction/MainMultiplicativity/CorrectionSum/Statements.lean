/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.CorrectionSum.Definitions

/-!
# NYLL correction-sum action-difference target

Modified by Worker 196, 13 November 2026: extract M056.004, lines 87–95 (proof omitted, lines 96–102) from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/CorrectionSum.lean` at `fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with
`Langlands.NYLL`, use focused imports and turn source theorems into Prop-valued
definitions without their proofs. See the paired Markdown for all changes and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

open scoped BigOperators

def frobeniusMultiplicativity_actionDifference_eq_correctionSumStatement
    {R : IntegralRepGroupType} [Group R] (B : Rep ℤ R)
    (τ₁ τ₄ : R) (p₁ p₃ p₄ : B.V) : Prop :=
    (B.ρ τ₄ p₄ - p₄) + (B.ρ τ₁ p₁ - p₁) +
        (p₃ - B.ρ (τ₄ * τ₁) p₃) =
      ∑ i : Fin 3,
        (B.ρ (frobeniusMultiplicativityCorrectionAction τ₁ τ₄ i)
          (frobeniusMultiplicativityCorrectionTerm B τ₁ p₁ p₃ p₄ i) -
          frobeniusMultiplicativityCorrectionTerm B τ₁ p₁ p₃ p₄ i)

end
end Langlands.NYLL.ClassFormation
