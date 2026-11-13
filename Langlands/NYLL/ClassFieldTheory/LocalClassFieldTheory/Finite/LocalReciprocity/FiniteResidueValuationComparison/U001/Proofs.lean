/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 256, with proof guidance by Worker 122 and the
   rank-one comparison argument of Worker 1199 (2026-11-13): adapt M251.001
   from upstream commit fbd320cd8b1b06487c58227e92eb135794267709,
   FiniteResidueValuationComparison.lean lines 33-59. Prefix the namespace
   with Langlands.NYLL, introduce the closed target telescope and use the
   published M233.007 restriction-extension theorem. Replace the upstream
   M245.018 fundamental-identity package by its published complete-DVF
   integral-closure existence consequence. Replace the unported M196.039
   comparison theorem by a local integral-closure containment and Mathlib
   rank-one overring proof, as in chosenLocalExtension_uniqueValuationExtension.
   Keep independent universes and use focused imports. Original LICENSE
   and NOTICE are retained in licenses/NYLL/. -/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueValuationComparison.Statement
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.U007.Proofs
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.StandardCompleteDVFExtensionProof

namespace Langlands.NYLL.LocalClassFieldTheory

open ValuationTheory RamificationTheory DiscreteValuationField

universe u v w

/-- M251.001: the restricted valuation ring equals any finite-separable extension ring. -/
theorem ValuationSubring.restrictIntermediateField_eq_of_finite_separable :
    ValuationSubring.restrictIntermediateField_eq_of_finite_separableStatement.{u, v, w} := by
  intro K Omega _ _ _ base A _ E _ _ C _
  let : _root_.Valuation.HasExtension base.valuation
      (A.restrictIntermediateField E).valuation :=
    RamificationTheory.ValuationSubring.restrictIntermediateField_hasExtension
      base.valuation A E
  obtain ⟨target, hExt, hIntegralClosure⟩ :=
    ValuedExtension.exists_integralClosure_standard_completeDVF_extension.{u, w, v}
      K E base
  let : _root_.Valuation.HasExtension base.valuation target.valuation := hExt
  let : IsIntegralClosure target.valuation.valuationSubring
      base.valuation.valuationSubring E := hIntegralClosure
  have hcomp : ∀ (D : _root_.ValuationSubring E)
      [_root_.Valuation.HasExtension base.valuation D.valuation],
      target.valuation.valuationSubring = D := by
    intro D _
    have hD : target.valuation.valuationSubring = D.valuation.valuationSubring := by
      apply _root_.ValuationSubring.eq_of_le_of_ne_top
      · intro z hz
        have hzIntegral : IsIntegral base.valuation.valuationSubring z :=
          (IsIntegralClosure.isIntegral_iff
            (A := target.valuation.valuationSubring)).mpr ⟨⟨z, hz⟩, rfl⟩
        exact (_root_.Valuation.valuationSubring.integers D.valuation).mem_of_integral
          (hzIntegral.tower_top (A := D.valuation.valuationSubring))
      · obtain ⟨a, ha⟩ := _root_.Valuation.IsNontrivial.exists_one_lt
          (v := base.valuation)
        intro hTop
        have hle : D.valuation (algebraMap K E a) ≤ 1 := by
          change algebraMap K E a ∈ D.valuation.valuationSubring
          rw [hTop]
          trivial
        exact (not_le_of_gt ha)
          ((_root_.Valuation.HasExtension.val_map_le_one_iff
            base.valuation D.valuation a).mp hle)
    simpa using hD
  exact (hcomp _).symm.trans (hcomp C)

end Langlands.NYLL.LocalClassFieldTheory
