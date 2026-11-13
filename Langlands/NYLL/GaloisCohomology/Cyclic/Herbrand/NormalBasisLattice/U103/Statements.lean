/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 232 from the NYLL pinned source units listed in the paired Markdown.
The namespace and imports are adapted. Source data bodies are unchanged;
source theorems are replaced by exact Prop-valued definitions.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U102.Definitions
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

def chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iffStatement
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
    {n : Nat}
    (u : 𝒪[L]ˣ) (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
    chosenNormalBasisPrincipalUnitLatticeClass K L n u hu = 0 ↔
      u ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1)

def chosenNormalBasisPrincipalUnitSet_mul_error_mem_succStatement
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
    {n : Nat}
    (hmul_succ : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈
            chosenBaseUniformizerPowSubmodule K L (n + 1) (chosenNormalBasisIntegerLattice K L))
    {u v : 𝒪[L]ˣ}
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (hv : v ∈ chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
    (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
        (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
          ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
      chosenBaseUniformizerPowSubmodule K L (n + 1)
        (chosenNormalBasisIntegerLattice K L)

def exists_chosenNormalBasisPrincipalUnitSet_mul_error_mem_succStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [FiniteDimensional K L]
    [IsGalois K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L] : Prop :=
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
          (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
              (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
                ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
            chosenBaseUniformizerPowSubmodule K L (n + 1)
              (chosenNormalBasisIntegerLattice K L)

def chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_addStatement
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
    {n : Nat}
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (u v : 𝒪[L]ˣ)
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (hv : v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (huv : u * v ∈ chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
    chosenNormalBasisPrincipalUnitLatticeClass K L n (u * v) huv =
      chosenNormalBasisPrincipalUnitLatticeClass K L n u hu +
        chosenNormalBasisPrincipalUnitLatticeClass K L n v hv

def exists_chosenNormalBasisPrincipalUnitSubgroupSuccPairStatement
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
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      ∃ Vn Vsucc : Subgroup 𝒪[L]ˣ,
        (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n ∧
        (Vsucc : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L (n + 1) ∧
        Vsucc ≤ Vn ∧
        Vn ≤ principalUnits L 1

end

end Langlands.NYLL.CyclicCohomology
