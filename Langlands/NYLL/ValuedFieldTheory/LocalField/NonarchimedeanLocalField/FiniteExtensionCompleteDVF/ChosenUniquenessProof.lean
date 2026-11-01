/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 1199 (2026-11-01): prove the published closed
   specialization of M248.011 from upstream commit
   fbd320cd8b1b06487c58227e92eb135794267709. Replace its invocation of the
   generic M196.021 uniqueness theorem by a direct proof using the accepted
   chosenLocalExtension_properties and Mathlib's dimension-one valuation-ring
   overring theorem. Obtain the chosen HasExtension and integral-closure
   instances locally. Preserve the named chosen valuation, the supplied
   algebra, and arbitrary comparison universe y. Prefix the namespace with
   Langlands.NYLL and use focused published imports. The original LICENSE
   and NOTICE are retained in licenses/NYLL/. -/

import Mathlib.RingTheory.Valuation.Integral
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenUniquenessStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenPropertiesProof

/-!
# Uniqueness of the chosen valuation on a finite local extension: proof

The chosen integral-closure valuation ring lies in every comparison valuation
ring. Its discrete rank one and the nontrivial base valuation force equality
of these rings and hence equivalence of the valuations.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe y

/-- Every extension of the canonical base valuation is equivalent to the
named chosen valuation, for any comparison value-group universe. -/
theorem chosenLocalExtension_uniqueValuationExtension :
    ChosenLocalExtensionUniqueValuationExtensionStatement.{y} := by
  intro K L _ _ _ _ _ _ _ _ Gamma' _ v' _
  obtain ⟨hExt, hIntegralClosure, _hFinite⟩ := chosenLocalExtension_properties K L
  let := hExt
  let := hIntegralClosure
  apply (_root_.Valuation.isEquiv_iff_valuationSubring _ _).mpr
  apply ValuationSubring.eq_of_le_of_ne_top
  · intro z hz
    have hzIntegral : IsIntegral (localCompleteDVF K).valuation.valuationSubring z :=
      (IsIntegralClosure.isIntegral_iff
        (A := (chosenLocalExtensionCompleteDVF K L).valuation.valuationSubring)).mpr
          ⟨⟨z, hz⟩, rfl⟩
    exact (_root_.Valuation.valuationSubring.integers v').mem_of_integral
      (hzIntegral.tower_top (A := v'.valuationSubring))
  · obtain ⟨a, ha⟩ := _root_.Valuation.IsNontrivial.exists_one_lt
      (v := (localCompleteDVF K).valuation)
    intro hTop
    have hle : v' (algebraMap K L a) ≤ 1 := by
      change algebraMap K L a ∈ v'.valuationSubring
      rw [hTop]
      trivial
    exact (not_le_of_gt ha)
      ((_root_.Valuation.HasExtension.val_map_le_one_iff
        (localCompleteDVF K).valuation v' a).mp hle)

end Langlands.NYLL.LocalFieldTheory
