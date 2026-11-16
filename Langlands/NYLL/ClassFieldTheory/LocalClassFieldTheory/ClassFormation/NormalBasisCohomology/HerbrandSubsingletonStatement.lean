/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract the exact M156.001 target from NYLL
-- fbd320cd, prefix the namespace and narrow imports. See the paired Markdown.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.PrincipalUnitSubgroupAction
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u
open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel
open CyclicCohomology.ProfiniteCohomology.Herbrand

-- Preserve the original generator hypothesis even though the target does not use its term.
set_option linter.unusedVariables false

/-- The local class-field-axiom theorem: for every sufficiently deep chosen normal-basis subgroup
`V`, both low-degree Herbrand quotients are trivial. -/
def exists_chosenNormalBasisPrincipalUnit_herbrand_subsingletonStatement
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
    [UniformSpace L]
    [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    (g : Gal(L/K))
    (hgen : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) : Prop :=
  ∃ c : Nat, ∀ n : Nat, c ≤ n →
    ∀ (V : Subgroup 𝒪[L]ˣ)
      (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n),
      letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction
        K L n V hV
      Subsingleton (HerbrandH0 (Gal(L / K)) V) ∧
        Subsingleton (HerbrandHMinusOne (Gal(L / K)) V g)

end

end Langlands.NYLL.LocalClassFieldTheory
