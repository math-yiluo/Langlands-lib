/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 369, 15 November 2026:
Extract the proof of M162.019 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 321 and 492-537).
Prefix the namespace with Langlands.NYLL, give the theorem the published
statement v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement K L x
as its type and unfold it first, and import the published modules of the
declarations the proof uses. The source's call of the theorem
v_inverseIntegerRingUniformizerFieldUnit (M133.019, IdealQuotients.lean
lines 277-285), whose proof is not in the Library, is replaced by a local
have-fact proved by that theorem's two-line source proof. The rest of the
source proof is unchanged. All other source declarations are omitted. The
upstream LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U019.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U018.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.U028.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U005.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U007.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U016.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U004.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U009.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U019.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm.U019.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

/-- Finite local reciprocity, normalized norm calculation for every finite separable
local-field extension: the normalized value of a field norm is the actual
residue degree times the upstairs normalized value. -/
theorem v_normUnits_eq_residue_finrank_mul_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (x : Lˣ) :
    v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement K L x := by
  unfold v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement
  -- Source M133.019 (`v_inverseIntegerRingUniformizerFieldUnit L`), proved here by its
  -- source proof (IdealQuotients.lean, lines 277-285).
  have hinvPrime :
      v L (Additive.ofMul (inverseIntegerRingUniformizerFieldUnit L)) = 1 := by
    rw [inverseIntegerRingUniformizerFieldUnit]
    exact v_integerRingIrreducibleFieldUnit_inv L
      (chosenIntegerRingUniformizer L) (chosenIntegerRingUniformizer_irreducible L)
      (integerRingUniformizerFieldUnit L) rfl
  let ϖ : Lˣ := inverseIntegerRingUniformizerFieldUnit L
  have hϖ : v L (Additive.ofMul ϖ) = 1 :=
    hinvPrime
  let n : Int := v L (Additive.ofMul x)
  let a : 𝒪[L]ˣ := uniformizerUnitFactor L ϖ hϖ x
  have haNorm :
      normUnits K L (integerUnitsToFieldUnits L a) =
        integerUnitsToFieldUnits K (normIntegerUnits K L a) := by
    apply Units.ext
    rfl
  have hx : integerUnitsToFieldUnits L a * ϖ ^ n = x := by
    exact uniformizerUnitFactor_mul_uniformizer_zpow L ϖ hϖ x
  have hxNorm :
      normUnits K L x =
        integerUnitsToFieldUnits K (normIntegerUnits K L a) *
          (normUnits K L ϖ) ^ n := by
    calc
      normUnits K L x =
          normUnits K L (integerUnitsToFieldUnits L a * ϖ ^ n) :=
        congrArg (normUnits K L) hx.symm
      _ = normUnits K L (integerUnitsToFieldUnits L a) *
          (normUnits K L ϖ) ^ n := by
        simp only [map_mul, map_zpow]
      _ = integerUnitsToFieldUnits K (normIntegerUnits K L a) *
          (normUnits K L ϖ) ^ n := by rw [haNorm]
  rw [hxNorm, v_mul, v_integerUnitsToFieldUnits, zero_add, v_zpow,
    v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable]
  simp only [n]
  ring

end

end Langlands.NYLL.LocalClassFieldTheory
