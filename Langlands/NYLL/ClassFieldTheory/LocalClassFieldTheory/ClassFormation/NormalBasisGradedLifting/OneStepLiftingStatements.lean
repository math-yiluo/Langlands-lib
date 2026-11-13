/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


-- Modified by Worker 197: extract the units listed in OneStepLiftingStatements.md from
-- NYLL fbd320cd8b1b06487c58227e92eb135794267709; preserve their exact targets
-- as Prop-valued definitions with explicit effective theorem telescopes.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel
open Filter
open CyclicCohomology.ProfiniteCohomology.Herbrand

set_option linter.unusedVariables false in
def exists_chosenNormalBasisPrincipalUnit_h0_oneStep_liftingStatement
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
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  ∃ c : Nat, ∀ k : Nat, c ≤ k → ∀ a : 𝒪[L]ˣ,
    a ∈ chosenNormalBasisPrincipalUnitSet K L k →
    (∀ sigma : Gal(L / K), sigma • a = a) →
    ∃ b a' : 𝒪[L]ˣ,
      b ∈ chosenNormalBasisPrincipalUnitSet K L k ∧
      a' ∈ chosenNormalBasisPrincipalUnitSet K L (k + 1) ∧
      (∀ sigma : Gal(L / K), sigma • a' = a') ∧
      a = tateNorm (Gal(L / K)) 𝒪[L]ˣ b * a'

set_option linter.unusedVariables false in
def exists_chosenNormalBasisPrincipalUnit_hMinusOne_oneStep_liftingStatement
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
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    (g : Gal(L/K)) (hgen : ∀ sigma : Gal(L/K),
      sigma ∈ Subgroup.zpowers g) : Prop :=
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  ∃ c : Nat, ∀ k : Nat, c ≤ k → ∀ a : 𝒪[L]ˣ,
    a ∈ chosenNormalBasisPrincipalUnitSet K L k →
    tateNorm (Gal(L / K)) 𝒪[L]ˣ a = 1 →
    ∃ b a' : 𝒪[L]ˣ,
      b ∈ chosenNormalBasisPrincipalUnitSet K L k ∧
      a' ∈ chosenNormalBasisPrincipalUnitSet K L (k + 1) ∧
      tateNorm (Gal(L / K)) 𝒪[L]ˣ a' = 1 ∧
      a = sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g b * a'

end

end Langlands.NYLL.LocalClassFieldTheory
