/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


-- Modified by Worker 197: extract the units listed in CorrectionProductLimitStatements.md from
-- NYLL fbd320cd8b1b06487c58227e92eb135794267709; preserve their exact targets
-- as Prop-valued definitions with explicit effective theorem telescopes.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U044.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.CorrectionProduct
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel
open Filter

set_option linter.unusedVariables false in
def chosenNormalBasisPrincipalUnitCorrectionProduct_memStatement
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
    (hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (d : Nat) : Prop :=
  chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d ∈
    chosenNormalBasisPrincipalUnitSet K L n

set_option linter.unusedVariables false in
def exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProduct_principalUnitStatement
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
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {b n : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) : Prop :=
  ∃ x : principalUnits L 1,
    Tendsto
      (fun d : Nat =>
        ((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]))
      atTop (nhds (((x : principalUnits L 1) : 𝒪[L]ˣ) : 𝒪[L]))

set_option linter.unusedVariables false in
def chosenNormalBasisPrincipalUnitCorrectionProduct_limit_memStatement
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
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    {n : Nat}
    (hclosed : IsClosed
      ((chosenBaseUniformizerPowSubmodule K L n
        (chosenNormalBasisIntegerLattice K L) : Set L)))
    (hmul : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        u * v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (z : Nat → 𝒪[L]ˣ)
    (hz : ∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i))
    (x : 𝒪[L]ˣ)
    (hx : Tendsto
      (fun d : Nat =>
        ((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d : 𝒪[L]ˣ) :
          𝒪[L]))
      atTop (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) : Prop :=
  x ∈ chosenNormalBasisPrincipalUnitSet K L n

set_option linter.unusedVariables false in
def exists_tendsto_chosenNormalBasisPrincipalUnitCorrectionProductStatement
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
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
  ∃ c : Nat, ∀ n : Nat, c ≤ n →
    ∀ z : Nat → 𝒪[L]ˣ,
      (∀ i : Nat, z i ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) →
        ∃ x : 𝒪[L]ˣ,
          Tendsto
              (fun d : Nat =>
                ((chosenNormalBasisPrincipalUnitCorrectionProduct (L := L) z d :
                  𝒪[L]ˣ) : 𝒪[L]))
              atTop (nhds ((x : 𝒪[L]ˣ) : 𝒪[L])) ∧
            x ∈ chosenNormalBasisPrincipalUnitSet K L n

end

end Langlands.NYLL.LocalClassFieldTheory
