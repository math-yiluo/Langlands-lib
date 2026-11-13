/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Rep.Basic
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# NYLL Frobenius multiplicativity correction data

Modified by Worker 196, 13 November 2026: extract M056.001, lines 32–35; M056.002, lines 40–42 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/CorrectionSum.lean` at `fbd320cd8b1b06487c58227e92eb135794267709`; prefix the namespace with
`Langlands.NYLL`, use focused imports and turn source theorems into Prop-valued
definitions without their proofs. See the paired Markdown for all changes and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

def frobeniusMultiplicativityCorrectionTerm
    {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (τ₁ : R) (p₁ p₃ p₄ : B.V) : Fin 3 → B.V :=
  ![p₄ - p₃, p₁ - p₃, p₃ - B.ρ τ₁ p₃]

def frobeniusMultiplicativityCorrectionAction {R : Type*} [Group R]
    (τ₁ τ₄ : R) : Fin 3 → R :=
  ![τ₄, τ₁, τ₄]

end
end Langlands.NYLL.ClassFormation
