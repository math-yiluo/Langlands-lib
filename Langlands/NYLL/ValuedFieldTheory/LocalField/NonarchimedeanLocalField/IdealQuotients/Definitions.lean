/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 201 on 2026-11-13: extracted M133.001 and M133.004
from IdealQuotients.lean at commit fbd320cd8b1b06487c58227e92eb135794267709;
added the Langlands.NYLL namespace prefix and reduced imports to Mathlib.
Both definition bodies, universes and telescopes are unchanged.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.NumberTheory.LocalField.Basic

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Additive identification of the integer ring modulo its maximal ideal with the residue field. -/
def integerRingModMaximalIdealAddEquivResidue
    (K : Type u) [Field K] [ValuativeRel K] :
    (𝒪[K] ⧸ (𝓂[K] : Ideal 𝒪[K])) ≃+ 𝓀[K] :=
  AddEquiv.refl _


/-- A chosen irreducible element of the integer ring of a nonarchimedean local field. -/
def chosenIntegerRingUniformizer
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : 𝒪[K] :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible 𝒪[K])


end
end Langlands.NYLL.LocalFieldTheory
