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
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U044.Definitions
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

def integerRingToFieldLinearMap_range_eqStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [ValuativeRel K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] : Prop :=
    LinearMap.range (integerRingToFieldLinearMap K L) =
      integerRingFieldSubmodule K L

def integerRingFieldSubmodule_fg_of_moduleFiniteStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [ValuativeRel K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
    (integerRingFieldSubmodule K L).FG

def exists_chosenBaseUniformizerPow_integerRingFieldSubmodule_le_chosenNormalBasisIntegerLatticeStatement
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
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n (integerRingFieldSubmodule K L) ≤
        chosenNormalBasisIntegerLattice K L

def exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mem_nhds_zeroStatement
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
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)) ∈ nhds (0 : L)

def exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_isClosedStatement
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
      IsClosed
        ((chosenBaseUniformizerPowSubmodule K L n
          (chosenNormalBasisIntegerLattice K L) : Set L))

def exists_chosenNormalBasisPrincipalUnitSet_inv_memStatement
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
      ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u⁻¹ ∈ chosenNormalBasisPrincipalUnitSet K L n

def exists_chosenNormalBasisPrincipalUnitSubgroupStatement
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
      ∃ V : Subgroup 𝒪[L]ˣ,
        (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n ∧
        V ≤ principalUnits L 1

end

end Langlands.NYLL.CyclicCohomology
