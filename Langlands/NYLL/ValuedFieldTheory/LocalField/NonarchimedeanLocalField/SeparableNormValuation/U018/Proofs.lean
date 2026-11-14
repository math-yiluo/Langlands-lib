/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 369, 14 November 2026:
Extract the proof of M162.018 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 321 and 473-490).
Prefix the namespace with Langlands.NYLL, give the theorem the published
statement v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement K L
as its type, and import the UniformizerNorm Statements module and the published
proof modules of M162.017 and M128.006. Because the target and the imported
theorems v_inv and M162.017 have statement constants as their types, the proof
first unfolds the target and rewrites with local have-statements obtained from
the imported theorems; the final simp only [neg_neg] becomes part of the
rewrite. All other source declarations are omitted. The upstream LICENSE and
NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.UniformizerNorm.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U017.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U006.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

/-- The norm of the positive generator (the inverse chosen prime element) has
base normalized value equal to the actual residue degree. -/
theorem v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement K L := by
  have hinv :
      v K (Additive.ofMul
          (normUnits K L (integerRingUniformizerFieldUnit L))⁻¹) =
        -v K (Additive.ofMul (normUnits K L (integerRingUniformizerFieldUnit L))) :=
    v_inv K _
  have hprime :
      v K (Additive.ofMul
          (normUnits K L (integerRingUniformizerFieldUnit L))) =
        -(Module.finrank 𝓀[K] 𝓀[L] : Int) :=
    v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable K L
  unfold v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement
  rw [inverseIntegerRingUniformizerFieldUnit, map_inv, hinv, hprime, neg_neg]

end

end Langlands.NYLL.LocalClassFieldTheory
