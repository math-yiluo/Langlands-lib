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

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U030.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U044.Definitions
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

def chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zeroStatement
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
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
    Tendsto
      (fun d : Nat => (-(((u : 𝒪[L]ˣ) : 𝒪[L]) - 1)) ^ (d + 1))
      atTop (nhds (0 : 𝒪[L]))

def chosenNormalBasisPrincipalUnitSet_inverseCorrectionProduct_tendsto_oneStatement
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
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
    Tendsto
      (fun d : Nat =>
        (((u : 𝒪[L]ˣ) : 𝒪[L]) : L) *
          (1 + inverseCorrectionPartialSum (L := L)
            ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d))
      atTop (nhds (1 : L))

def chosenNormalBasisPrincipalUnitSet_one_add_inverseCorrection_tendsto_invStatement
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
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
    Tendsto
      (fun d : Nat =>
        1 + inverseCorrectionPartialSum (L := L)
          ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d)
      atTop (nhds ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L)))

def chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_oneStatement
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
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
    Tendsto
      (fun d : Nat =>
        inverseCorrectionPartialSum (L := L)
          ((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) d)
      atTop (nhds (((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) - 1)))

def chosenNormalBasisPrincipalUnitSet_inverse_sub_one_mem_of_closedStatement
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
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n
            (chosenNormalBasisIntegerLattice K L))
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
    ((((u⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)

def chosenNormalBasisPrincipalUnitSet_inv_mem_of_closedStatement
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
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hle : chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
      maximalIdealFieldSubmodule K L)
    (hmul : ∀ x : L,
      x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
      ∀ y : L,
        y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
          x * y ∈ chosenBaseUniformizerPowSubmodule K L n
            (chosenNormalBasisIntegerLattice K L))
    {u : 𝒪[L]ˣ} (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n) : Prop :=
    u⁻¹ ∈ chosenNormalBasisPrincipalUnitSet K L n

def exists_chosenNormalBasisPrincipalUnitSet_inv_mem_of_closedStatement
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
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] : Prop :=
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      IsClosed
        ((chosenBaseUniformizerPowSubmodule K L n
          (chosenNormalBasisIntegerLattice K L) : Set L)) →
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u⁻¹ ∈ chosenNormalBasisPrincipalUnitSet K L n

end

end Langlands.NYLL.CyclicCohomology
