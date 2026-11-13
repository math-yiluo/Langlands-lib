/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: state only M161.035, the theorem
galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuation
at lines 780–792 of upstream commit fbd320cd8b1b06487c58227e92eb135794267709,
as the closed proposition definition
galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuationStatement;
prefix the namespace with Langlands.NYLL; replace the source imports by the two
published modules that define the residue homomorphism and the unramified class.
The parameters, hypotheses and conclusion are otherwise unchanged. No proof is
given here. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.AlgebraDefinitions

/-!
# Bijectivity of the residue action of an unramified extension: target

This module states only M161.035, lines 780–792 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/FiniteUnramified.lean`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Closed target for NYLL M161.035: for a finite Galois extension of
nonarchimedean local fields that is unramified at the maximal ideals, the
residue action `Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L])` is bijective. -/
def galoisGroupResidueAlgEquivHomOfIsIntegralClosure_bijective_of_unramifiedValuationStatement :
    Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L],
    Function.Bijective (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L)

end Langlands.NYLL.LocalFieldTheory
