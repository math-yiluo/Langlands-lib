/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: extract only M161.036, the definition
galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure at
lines 794–806 of upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL; the bijectivity input is the published
adapted theorem of M161.035 applied to the same parameters; replace the source
imports by the published proof module. The parameters, result type and body are
otherwise unchanged. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueBijectiveProof

/-!
# The Galois-to-residue isomorphism of an unramified extension

This module adapts only M161.036, lines 794–806 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean`.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The integral-closure residue action of a finite Galois unramified extension of
nonarchimedean local fields, as a group isomorphism
`Gal(L/K) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])`. -/
def galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L / K) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  MulEquiv.ofBijective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)
    (galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation K L)

end

end Langlands.NYLL.LocalFieldTheory
