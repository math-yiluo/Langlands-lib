/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 1199 (2026-11-01): prove the published grouped
   target of M248.003 and M248.004 from upstream commit
   fbd320cd8b1b06487c58227e92eb135794267709 at independent universes u/v.
   Replace the generic uniqueness chain by the published full-universe
   integral-closure existence theorem and a local dimension-one overring
   comparison. Build IsIntegralClosure for the actual supplied upstairs
   valuation subring and use Mathlib's IsIntegralClosure.finite. Preserve
   the supplied algebra and its HasExtension-induced ring scalars, prefix
   the namespace with Langlands.NYLL, and use focused published imports.
   The original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.Integral
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.IntegerRingPropertiesStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ExtensionProof
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.StandardCompleteDVFExtensionProof

/-!
# Canonical integer rings in finite separable local extensions: proof

The supplied upstairs valuation ring equals the integral-closure valuation
ring supplied by complete-DVF existence. Thus the actual upstairs ring is
the integral closure and is finite over the actual base valuation ring.
-/

namespace Langlands.NYLL.LocalFieldTheory

open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v

/-- The actual canonical integer ring of a finite separable local extension
is the integral closure of the base integer ring and is finite over it. -/
theorem localCompleteDVF_integerRing_properties :
    LocalCompleteDVFIntegerRingPropertiesStatement.{u, v} := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _
  let : _root_.Valuation.HasExtension
      (localCompleteDVF K).valuation (localCompleteDVF L).valuation :=
    localCompleteDVFValuation_hasExtension K L
  obtain ⟨target, hExt, hIntegralClosure⟩ :=
    exists_integralClosure_standard_completeDVF_extension.{u, u, v}
      K L (localCompleteDVF K)
  let := hExt
  let := hIntegralClosure
  have hEq : target.valuation.valuationSubring =
      (localCompleteDVF L).valuation.valuationSubring := by
    apply ValuationSubring.eq_of_le_of_ne_top
    · intro z hz
      have hzIntegral : IsIntegral (localCompleteDVF K).valuation.valuationSubring z :=
        (IsIntegralClosure.isIntegral_iff
          (A := target.valuation.valuationSubring)).mpr ⟨⟨z, hz⟩, rfl⟩
      exact (_root_.Valuation.valuationSubring.integers
        (localCompleteDVF L).valuation).mem_of_integral
          (hzIntegral.tower_top
            (A := (localCompleteDVF L).valuation.valuationSubring))
    · obtain ⟨a, ha⟩ := _root_.Valuation.IsNontrivial.exists_one_lt
        (v := (localCompleteDVF K).valuation)
      intro hTop
      have hle : (localCompleteDVF L).valuation (algebraMap K L a) ≤ 1 := by
        change algebraMap K L a ∈ (localCompleteDVF L).valuation.valuationSubring
        rw [hTop]
        trivial
      exact (not_le_of_gt ha)
        ((_root_.Valuation.HasExtension.val_map_le_one_iff
          (localCompleteDVF K).valuation (localCompleteDVF L).valuation a).mp hle)
  change IsIntegralClosure (localCompleteDVF L).valuation.valuationSubring
      (localCompleteDVF K).valuation.valuationSubring L ∧
    Module.Finite (localCompleteDVF K).valuation.valuationSubring
      (localCompleteDVF L).valuation.valuationSubring
  have hActual : IsIntegralClosure
      (localCompleteDVF L).valuation.valuationSubring
      (localCompleteDVF K).valuation.valuationSubring L := by
    refine { algebraMap_injective := ?_, isIntegral_iff := ?_ }
    · intro x y hxy
      exact Subtype.ext hxy
    · intro z
      constructor
      · intro hz
        obtain ⟨a, rfl⟩ := (IsIntegralClosure.isIntegral_iff
          (A := target.valuation.valuationSubring)).mp hz
        have ha : (a : L) ∈ (localCompleteDVF L).valuation.valuationSubring := by
          rw [← hEq]
          exact a.2
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro ⟨a, rfl⟩
        have ha : (a : L) ∈ target.valuation.valuationSubring := by
          rw [hEq]
          exact a.2
        exact (IsIntegralClosure.isIntegral_iff
          (A := target.valuation.valuationSubring)).mpr ⟨⟨a, ha⟩, rfl⟩
  let := hActual
  exact ⟨hActual, IsIntegralClosure.finite
    (localCompleteDVF K).valuation.valuationSubring K L
    (localCompleteDVF L).valuation.valuationSubring⟩

end Langlands.NYLL.LocalFieldTheory
