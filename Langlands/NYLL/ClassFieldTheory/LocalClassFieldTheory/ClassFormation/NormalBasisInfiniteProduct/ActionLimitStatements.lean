/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M150.005/.006 from NYLL commit
-- fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued targets,
-- prefix the namespace and reduce imports. See ActionLimitStatements.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation.IntegerDefinitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions
import Mathlib.NumberTheory.LocalField.Basic

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter
open CyclicCohomology.ProfiniteCohomology.Herbrand

set_option linter.unusedVariables false in
/-- The source target for convergence of finite Tate norms of integer units. -/
def tendsto_galoisGroupIntegerUnits_tateNorm_of_tendstoStatement
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [ValuativeRel K] [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (f : Nat → 𝒪[L]ˣ) (x : 𝒪[L]ˣ)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) : Prop :=
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  Tendsto
    (fun d : Nat =>
      ((tateNorm (Gal(L / K)) 𝒪[L]ˣ (f d) : 𝒪[L]ˣ) : 𝒪[L]))
    atTop
    (nhds ((tateNorm (Gal(L / K)) 𝒪[L]ˣ x : 𝒪[L]ˣ) : 𝒪[L]))

set_option linter.unusedVariables false in
/-- The source target for convergence of multiplicative Galois coboundaries. -/
def tendsto_galoisGroupIntegerUnits_sigmaMinusOne_of_tendstoStatement
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [UniformSpace L] [IsUniformAddGroup L] [IsNonarchimedeanLocalField L]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (g : Gal(L/K)) (f : Nat → 𝒪[L]ˣ) (x : 𝒪[L]ˣ)
    (hf : Tendsto (fun d : Nat => ((f d : 𝒪[L]ˣ) : 𝒪[L])) atTop
      (nhds ((x : 𝒪[L]ˣ) : 𝒪[L]))) : Prop :=
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  Tendsto
    (fun d : Nat =>
      ((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g (f d) : 𝒪[L]ˣ) : 𝒪[L]))
    atTop
    (nhds ((sigmaMinusOne (Gal(L / K)) 𝒪[L]ˣ g x : 𝒪[L]ˣ) : 𝒪[L]))

end

end Langlands.NYLL.LocalClassFieldTheory
