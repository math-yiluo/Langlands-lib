/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M149.001–.003 from NYLL fbd320cd as
-- Prop-valued targets, prefix the namespace and use published focused imports.
-- See Statements.md for the complete source correspondence.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.PrincipalUnitSubgroupAction
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.IntegerUnitsQuotAction
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.IntegerUnitMaps
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel
open CyclicCohomology.ProfiniteCohomology.Herbrand

-- Source proof inputs stay explicit even when absent from a target's body.
set_option linter.unusedVariables false

/-- The normal-basis subgroup sequence is short exact and equivariant for
the actual actions used in the local class-field-axiom argument. -/
def chosenNormalBasisIntegerUnitsHerbrand_shortExactStatement
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
  letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  (∀ (sigma : Gal(L / K)) (a : V),
      chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V (sigma • a) =
        sigma • chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V a) ∧
    (∀ (sigma : Gal(L / K)) (a : 𝒪[L]ˣ),
      chosenNormalBasisIntegerUnitsQuotientMap (L := L) V (sigma • a) =
        sigma • chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a) ∧
    (∀ a : 𝒪[L]ˣ,
      chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a = 1 ↔
        ∃ v : V,
          chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V v = a) ∧
    Function.Injective
      (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V) ∧
    Function.Surjective
      (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V)

/-- Integer-unit Herbrand calculation at one chosen normal-basis
level.  The only low-degree cohomology input is the proved vanishing of
`H⁰(G,V)` and `H⁻¹(G,V)`; finiteness of `𝒪_Lˣ/V` is the other honest
input. -/
def integerUnits_herbrandQuotient_eq_one_of_chosenNormalBasisStatement
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hfinite : Finite (𝒪[L]ˣ ⧸ V))
    (g : Gal(L/K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g)
    (hH0 :
      letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
      Subsingleton (HerbrandH0 (Gal(L / K)) V))
    (hHminusOne :
      letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
      Subsingleton (HerbrandHMinusOne (Gal(L / K)) V g)) : Prop :=
  letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  ∃ hU : HerbrandQuotientDefined (Gal(L / K)) 𝒪[L]ˣ g,
    @herbrandQuotient (Gal(L / K)) 𝒪[L]ˣ _ _ _
      (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
      g hU.1 hU.2 = 1

/-- At all sufficiently deep chosen normal-basis levels:
`H⁰(G,V)=H⁻¹(G,V)=1` implies that the integer-unit Herbrand quotient is
defined and equals `1`. -/
def exists_integerUnits_herbrandQuotient_eq_one_of_large_chosenNormalBasisLevelStatement
    (K L : Type)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
  ∃ c : Nat, ∀ n : Nat, c ≤ n →
    ∀ (V : Subgroup 𝒪[L]ˣ)
      (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
      (g : Gal(L / K)),
      (∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) →
      (letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV;
        Subsingleton (HerbrandH0 (Gal(L / K)) V)) →
      (letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV;
        Subsingleton (HerbrandHMinusOne (Gal(L / K)) V g)) →
      letI := chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction K L n V hV
      letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
      letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
      ∃ hU : HerbrandQuotientDefined (Gal(L / K)) 𝒪[L]ˣ g,
        @herbrandQuotient (Gal(L / K)) 𝒪[L]ˣ _ _ _
          (galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L)
          g hU.1 hU.2 = 1

end

end Langlands.NYLL.LocalClassFieldTheory
