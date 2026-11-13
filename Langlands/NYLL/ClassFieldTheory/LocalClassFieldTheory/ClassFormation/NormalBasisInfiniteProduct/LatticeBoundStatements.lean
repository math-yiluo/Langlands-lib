/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


-- Modified by Worker 197: extract the units listed in LatticeBoundStatements.md from
-- NYLL fbd320cd8b1b06487c58227e92eb135794267709; preserve their exact targets
-- as Prop-valued definitions with explicit effective theorem telescopes.

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U044.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U059.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel
open Filter

set_option linter.unusedVariables false in
def chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_powStatement
    (K L : Type u)
    [Field K]
    [Field L]
    [Algebra K L]
    [ValuativeRel K]
    [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (m : Nat) {x : L}
    (hx : x ∈ chosenBaseUniformizerPowSubmodule K L m
      (integerRingFieldSubmodule K L)) : Prop :=
  ∃ a : 𝒪[L], a ∈ (𝓂[L] ^ m : Ideal 𝒪[L]) ∧ (a : L) = x

set_option linter.unusedVariables false in
def chosenNormalBasisPrincipalUnitSet_mem_principalUnits_succ_of_lattice_boundStatement
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
    {b n i : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b
        (chosenNormalBasisIntegerLattice K L) ≤
      integerRingFieldSubmodule K L)
    (hbn : b + 1 ≤ n) {z : 𝒪[L]ˣ}
    (hz : z ∈ chosenNormalBasisPrincipalUnitSet K L (n + i)) : Prop :=
  z ∈ principalUnits L (1 + i)

set_option linter.unusedVariables false in
def tendsto_chosenNormalBasisPrincipalUnitSequence_one_of_lattice_boundStatement
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
  Tendsto (fun i : Nat => ((z i : 𝒪[L]ˣ) : 𝒪[L])) atTop
    (nhds (1 : 𝒪[L]))

end

end Langlands.NYLL.LocalClassFieldTheory
