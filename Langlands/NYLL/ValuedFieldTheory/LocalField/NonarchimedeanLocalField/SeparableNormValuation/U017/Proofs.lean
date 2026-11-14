/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 369, 14 November 2026:
Extract the proof of M162.017 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 321 and 412-471).
Prefix the namespace with Langlands.NYLL, give the theorem the published
statement v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement K L
as its type, and import the UniformizerNorm Statements module and the published
proof modules of M162.016, M133.005, M133.006, M133.015, M133.022, M128.004,
M128.005 and M128.019. Because M128.008 (v_pow) is not yet published, it is
proved here as the private theorem v_pow_of_v_mul_v_one by induction from
v_one and v_mul; M133.018 (v_integerRingUniformizerFieldUnit) is replaced by its
source proof term, an application of M133.015 and M133.005. The step using
M162.016 is an exact term instead of simpa, and the final rewrites at the
valuation equation use local have-statements, since the imported theorems have
statement constants as their types. All other source declarations are
omitted. The upstream LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.UniformizerNorm.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U016.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U005.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U006.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U015.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U022.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U004.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U005.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U019.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

/-- The normalized valuation of a natural power of a field unit (the statement of
source unit M128.008 `v_pow`, proved here by induction from `v_one` and `v_mul`). -/
private theorem v_pow_of_v_mul_v_one
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Nat) :
    v K (Additive.ofMul (x ^ n)) = (n : Int) * v K (Additive.ofMul x) := by
  induction n with
  | zero =>
      have hone : v K (Additive.ofMul (1 : Kˣ)) = 0 := v_one K
      rw [pow_zero, hone, Nat.cast_zero, zero_mul]
  | succ n ih =>
      have hmul : v K (Additive.ofMul (x ^ n * x)) =
          v K (Additive.ofMul (x ^ n)) + v K (Additive.ofMul x) := v_mul K (x ^ n) x
      rw [pow_succ, hmul, ih, Nat.cast_succ, add_mul, one_mul]

/-- The norm of the chosen upstairs prime element has base normalized value
the negative of the actual residue degree, for every finite separable
extension (not only a Galois one). -/
theorem v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement K L := by
  let : Module.Finite 𝒪[K] 𝒪[L] :=
    IsIntegralClosure.finite 𝒪[K] K L 𝒪[L]
  let f : Nat := Module.finrank 𝓀[K] 𝓀[L]
  have hspan :
      Ideal.span
          (Set.singleton (Algebra.intNorm 𝒪[K] 𝒪[L]
            (chosenIntegerRingUniformizer L))) =
        Ideal.span (Set.singleton (chosenIntegerRingUniformizer K ^ f)) := by
    calc
      Ideal.span
          (Set.singleton (Algebra.intNorm 𝒪[K] 𝒪[L]
            (chosenIntegerRingUniformizer L))) =
          Ideal.relNorm 𝒪[K]
            (Ideal.span ({chosenIntegerRingUniformizer L} : Set 𝒪[L])) := by
        exact (Ideal.spanNorm_singleton (R := 𝒪[K])
          (r := chosenIntegerRingUniformizer L)).symm
      _ = Ideal.relNorm 𝒪[K] (𝓂[L] : Ideal 𝒪[L]) := by
        rw [chosenIntegerRingUniformizer_maximalIdeal_eq L]
      _ = (𝓂[K] : Ideal 𝒪[K]) ^ f := by
        exact relNorm_maximalIdeal_eq_pow_residue_finrank K L
      _ = Ideal.span (Set.singleton (chosenIntegerRingUniformizer K ^ f)) :=
        maximalIdeal_pow_eq_span_uniformizer_pow K f
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hfieldUnits :
      normUnits K L (integerRingUniformizerFieldUnit L) *
        integerUnitsToFieldUnits K u =
      integerRingUniformizerFieldUnit K ^ f := by
    apply Units.ext
    have huField := congrArg (algebraMap 𝒪[K] K) hu
    rw [map_mul, Algebra.algebraMap_intNorm (K := K) (L := L)] at huField
    change
      Algebra.norm K (algebraMap 𝒪[L] L (chosenIntegerRingUniformizer L)) *
          algebraMap 𝒪[K] K (u : 𝒪[K]) =
        algebraMap 𝒪[K] K (chosenIntegerRingUniformizer K) ^ f
    exact huField
  have hvalue := congrArg
    (fun z : Kˣ => v K (Additive.ofMul z)) hfieldUnits
  change v K (Additive.ofMul
      (normUnits K L (integerRingUniformizerFieldUnit L) *
        integerUnitsToFieldUnits K u)) =
    v K (Additive.ofMul (integerRingUniformizerFieldUnit K ^ f)) at hvalue
  have hmul :
      v K (Additive.ofMul
          (normUnits K L (integerRingUniformizerFieldUnit L) *
            integerUnitsToFieldUnits K u)) =
        v K (Additive.ofMul (normUnits K L (integerRingUniformizerFieldUnit L))) +
          v K (Additive.ofMul (integerUnitsToFieldUnits K u)) :=
    v_mul K _ _
  have hunit : v K (Additive.ofMul (integerUnitsToFieldUnits K u)) = 0 :=
    v_integerUnitsToFieldUnits K u
  -- The source theorem `v_integerRingUniformizerFieldUnit K` (M133.018), whose
  -- source proof is this single application of M133.015 and M133.005.
  have hprime : v K (Additive.ofMul (integerRingUniformizerFieldUnit K)) = -1 :=
    v_integerRingIrreducibleFieldUnit K (chosenIntegerRingUniformizer K)
      (chosenIntegerRingUniformizer_irreducible K)
      (integerRingUniformizerFieldUnit K) rfl
  rw [hmul, hunit, add_zero, v_pow_of_v_mul_v_one, hprime] at hvalue
  unfold v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement
  rw [hvalue, mul_neg_one]

end

end Langlands.NYLL.LocalClassFieldTheory
