/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


-- Modified by Worker 197: extract the units listed in FiniteBoundaryStatements.md from
-- NYLL fbd320cd8b1b06487c58227e92eb135794267709; preserve their exact targets
-- as Prop-valued definitions with explicit effective theorem telescopes.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel
open Filter

set_option linter.unusedVariables false in
def exists_principalUnits_le_chosenNormalBasisPrincipalUnitSetStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
  ∃ c : Nat, ∀ n : Nat, c ≤ n →
    ∃ m : Nat, (principalUnits L m : Set 𝒪[L]ˣ) ⊆
      chosenNormalBasisPrincipalUnitSet K L n

set_option linter.unusedVariables false in
def exists_finite_chosenNormalBasisIntegerUnitsQuotientStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
  ∃ c : Nat, ∀ n : Nat, c ≤ n →
    ∀ (V : Subgroup 𝒪[L]ˣ),
      (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n →
        Finite (𝒪[L]ˣ ⧸ V)

end

end Langlands.NYLL.LocalClassFieldTheory
