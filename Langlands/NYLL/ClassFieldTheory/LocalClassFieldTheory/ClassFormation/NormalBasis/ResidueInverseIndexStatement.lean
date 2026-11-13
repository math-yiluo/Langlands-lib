/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.ResidueInverseIndex

/-!
Adapted by Worker 197 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
Evaluation target for inverse-index residue coordinates
See the paired Markdown for exact source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open LocalFieldTheory

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L]

def chosenNormalBasisPiResidueInverseIndexAddEquiv_applyStatement
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (f : Gal(L/K) → (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])))
    (σ : Gal(L/K)) : Prop :=
  chosenNormalBasisPiResidueInverseIndexAddEquiv K L f σ =
      integerRingModMaximalIdealAddEquivResidue K (f σ⁻¹)

end

end Langlands.NYLL.LocalClassFieldTheory
