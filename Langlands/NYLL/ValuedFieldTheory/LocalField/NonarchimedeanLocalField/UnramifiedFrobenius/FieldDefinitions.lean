/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: extract only M264.007, the definition
arithmeticFrobeniusOfUnramifiedValuation at lines 126–139 of upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL; replace the source imports by the two published modules that
define its ingredients. The parameters, result type and body are otherwise
unchanged. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueEquivDefinitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius.ResidueDefinitions

/-!
# Arithmetic Frobenius of a finite unramified extension

This module adapts only M264.007, lines 126–139 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean`.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Arithmetic Frobenius in `Gal(L/K)` of a finite Galois unramified extension of
nonarchimedean local fields: the unique automorphism whose residue action is the
residue arithmetic Frobenius `x ↦ x ^ #𝓀[K]`. -/
def arithmeticFrobeniusOfUnramifiedValuation
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Gal(L / K) :=
  (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).symm
    (residueExtensionArithmeticFrobeniusOfValuationExtension K L)

end

end Langlands.NYLL.LocalFieldTheory
