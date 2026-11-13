/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 231 on 2026-11-13: extracted the listed theorem types
as Prop-valued definitions, removed their proofs, prefixed the namespace
with Langlands.NYLL and reduced imports. See the paired source map.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U002.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U014.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U044.Definitions

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

set_option linter.unusedVariables false

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable [ValuativeRel K]

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open LocalFieldTheory

variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [FiniteDimensional K L] [IsGalois K L] in
def integerRingMap_uniformizer_mem_maximalIdeal_of_valuationExtensionStatement : Prop :=
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K) ∈
      (𝓂[L] : Ideal 𝒪[L])

omit [FiniteDimensional K L] [IsGalois K L] in
def exists_chosenBaseUniformizerPow_mul_mem_integerRing_of_valuationExtensionStatement (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (x : L) : Prop :=
    ∃ n : Nat,
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * x ∈ 𝒪[L]

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
def mem_integerRingFieldSubmodule_iffStatement (x : L) : Prop :=
    x ∈ integerRingFieldSubmodule K L ↔ x ∈ 𝒪[L]

omit [FiniteDimensional K L] [IsGalois K L] in
def chosenBaseUniformizerPow_integerRingFieldSubmodule_mem_nhds_zeroStatement
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (m : Nat) : Prop :=
    ((chosenBaseUniformizerPowSubmodule K L m
      (integerRingFieldSubmodule K L) : Set L)) ∈ nhds (0 : L)

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
def mem_maximalIdealFieldSubmodule_iffStatement (x : L) : Prop :=
    x ∈ maximalIdealFieldSubmodule K L ↔
      ∃ a : 𝒪[L], a ∈ (𝓂[L] : Ideal 𝒪[L]) ∧ (a : L) = x

omit [FiniteDimensional K L] [IsGalois K L] in
def exists_chosenBaseUniformizerPowSubmodule_le_integerRingFieldSubmodule_of_fgStatement
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {N : Submodule 𝒪[K] L} (hN : N.FG) : Prop :=
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n N ≤ integerRingFieldSubmodule K L

def exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_integerRingFieldSubmoduleStatement
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] : Prop :=
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
        integerRingFieldSubmodule K L

omit [FiniteDimensional K L] [IsGalois K L] in
def chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmoduleStatement
    {N : Submodule 𝒪[K] L} {b : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b N ≤ integerRingFieldSubmodule K L) : Prop :=
    chosenBaseUniformizerPowSubmodule K L (b + 1) N ≤
      maximalIdealFieldSubmodule K L

omit [FiniteDimensional K L] [IsGalois K L] in
def exists_chosenBaseUniformizerPowSubmodule_le_maximalIdealFieldSubmodule_of_fgStatement
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    {N : Submodule 𝒪[K] L} (hN : N.FG) : Prop :=
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n N ≤ maximalIdealFieldSubmodule K L

def exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdealFieldSubmoduleStatement
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] : Prop :=
    ∃ n : Nat,
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
        maximalIdealFieldSubmodule K L

def exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closedStatement
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] : Prop :=
    ∃ c : Nat, ∀ n : Nat, c ≤ n →
      chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) ≤
        maximalIdealFieldSubmodule K L ∧
      ∀ x : L,
        x ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
        ∀ y : L,
          y ∈ chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L) →
            x * y ∈
              chosenBaseUniformizerPowSubmodule K L n (chosenNormalBasisIntegerLattice K L)

end
end Langlands.NYLL.CyclicCohomology
