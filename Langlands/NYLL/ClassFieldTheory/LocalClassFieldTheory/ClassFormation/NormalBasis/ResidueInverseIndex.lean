/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Definitions
import Mathlib.FieldTheory.Galois.Basic

/-!
Adapted by Worker 197 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
Residue coordinate equivalence with inverse Galois index
See the paired Markdown for exact source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

open LocalFieldTheory

variable (K L : Type u) [Field K] [ValuativeRel K] [Field L]
  [Algebra K L]

def chosenNormalBasisPiResidueInverseIndexAddEquiv :
    (Gal(L / K) → (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K]))) ≃+
      (Gal(L / K) → 𝓀[K]) where
  toFun f σ := integerRingModMaximalIdealAddEquivResidue K (f σ⁻¹)
  invFun f σ := (integerRingModMaximalIdealAddEquivResidue K).symm (f σ⁻¹)
  left_inv := by
    intro f
    funext σ
    simp only [inv_inv, AddEquiv.symm_apply_apply]
  right_inv := by
    intro f
    funext σ
    simp only [inv_inv, AddEquiv.apply_symm_apply]
  map_add' := by
    intro f g
    funext σ
    exact map_add (integerRingModMaximalIdealAddEquivResidue K) (f σ⁻¹) (g σ⁻¹)

end

end Langlands.NYLL.LocalClassFieldTheory
