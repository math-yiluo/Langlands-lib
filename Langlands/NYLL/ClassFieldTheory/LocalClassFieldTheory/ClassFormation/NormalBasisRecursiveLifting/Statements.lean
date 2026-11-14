/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 111, 14 November 2026: extract the theorem units M155.002
and M155.003 of NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisRecursiveLifting.lean`
(lines 53–62 and 149–160), as Prop-valued definitions with the `Statement`
suffix, prefix the namespaces with `Langlands.NYLL`, write the section-variable
telescope (source lines 34–40) as explicit binders, reuse the published data by
Lean name and reduce the imports. Universes, binders, the `letI` action and the
propositions are unchanged; no proof is supplied. See the paired Markdown; the
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Recursive lifting on the normal-basis principal-unit filtration: statements

The exact propositions of the two source theorems asserting that, at every
sufficiently deep normal-basis level, a Galois-fixed integer unit is a Tate
norm, and (for a generator of the Galois group) a norm-one integer unit is a
multiplicative coboundary, from the same level.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Source M155.002 (recursive `H⁰` lifting): there is a level `c` such that
for every `n ≥ c`, every Galois-fixed integer unit in the `n`-th normal-basis
principal-unit set is the Tate norm of an integer unit in the same set. -/
def exists_chosenNormalBasisPrincipalUnit_fixed_is_tateNormStatement
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ a : 𝒪[L]ˣ,
    a ∈ chosenNormalBasisPrincipalUnitSet K L n →
    (∀ sigma : Gal(L / K), sigma • a = a) →
    ∃ b : 𝒪[L]ˣ, b ∈ chosenNormalBasisPrincipalUnitSet K L n ∧
      a = tateNorm (Gal(L / K)) 𝒪[L]ˣ b

set_option linter.unusedVariables false in
/-- Source M155.003 (recursive `H⁻¹` lifting): for a generator `g` of the
Galois group there is a level `c` such that for every `n ≥ c`, every integer
unit of Tate norm one in the `n`-th normal-basis principal-unit set is the
coboundary `g • b * b⁻¹` of an integer unit `b` in the same set. -/
def exists_chosenNormalBasisPrincipalUnit_normOne_is_sigmaMinusOneStatement
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    (g : Gal(L/K)) (hgen : ∀ sigma : Gal(L / K),
      sigma ∈ Subgroup.zpowers g) : Prop :=
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  ∃ c : Nat, ∀ n : Nat, c ≤ n → ∀ a : 𝒪[L]ˣ,
    a ∈ chosenNormalBasisPrincipalUnitSet K L n →
    tateNorm (Gal(L / K)) 𝒪[L]ˣ a = 1 →
    ∃ b : 𝒪[L]ˣ, b ∈ chosenNormalBasisPrincipalUnitSet K L n ∧
      a = sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g b

end

end Langlands.NYLL.LocalClassFieldTheory
