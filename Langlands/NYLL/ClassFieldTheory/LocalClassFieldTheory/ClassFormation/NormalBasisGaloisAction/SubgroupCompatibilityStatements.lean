/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract the M145.008/.009/.015 statements from
-- NYLL fbd320cd as Prop definitions with their complete source telescopes,
-- prefix the namespace and narrow imports. See the paired Markdown.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.PrincipalUnitSubgroupAction
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.IntegerUnitMaps
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel
open CyclicCohomology.ProfiniteCohomology.Herbrand

/-- Coercing the subgroup Tate norm gives the ambient product over the Galois group. -/
def chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coeStatement
    (K L : Type u)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (a : V) : Prop :=
  letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  ((tateNorm (Gal(L / K)) V a : V) : 𝒪[L]ˣ) =
    tateNorm (Gal(L / K)) 𝒪[L]ˣ (a : 𝒪[L]ˣ)

/-- Coercion commutes with the `σ - 1` operation on the principal-unit subgroup. -/
def chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coeStatement
    (K L : Type u)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (sigma : Gal(L/K)) (a : V) : Prop :=
  letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  ((sigmaMinusOne (Gal(L / K)) V sigma a : V) : 𝒪[L]ˣ) =
    sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ sigma (a : 𝒪[L]ˣ)

/-- Inclusion of the principal-unit subgroup is Galois equivariant. -/
def chosenNormalBasisPrincipalUnitSubgroupInclusion_equivariantStatement
    (K L : Type u)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (sigma : Gal(L/K)) (a : V) : Prop :=
  letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V (sigma • a) =
    sigma • chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V a

end

end Langlands.NYLL.LocalClassFieldTheory
