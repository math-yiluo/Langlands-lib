/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 133 (2026-11-13): extract only the proof of M110.017 from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean
(lines 376–413) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published ValuationSubringStatements module
of Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
and state the theorem as that module's `valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdealStatement`
applied to the source binders, opening it with `unfold` before the
unchanged source tactic proof. Only the field L : Type v of the source
section is used, so the section variables are cut down to {L : Type v}
[Field L] and universe v; the noncomputable section and the open
ResidueField namespace are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.ValuationSubringStatements

/-!
# A valuation overring centred at the maximal ideal is equal (NYLL M110.017)

If `R ≤ S` are valuation subrings of `L` and the prime `idealOfLE R S` of `R`
corresponding to `S` is the maximal ideal of `R`, then `S = R`.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

universe v

variable {L : Type v} [Field L]

/-- A valuation overring of a valuation subring is equal to it when the
corresponding localization prime is the maximal ideal of the smaller valuation
subring. -/
theorem valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal
    (R S : ValuationSubring L) (hRS : R ≤ S)
    (hcenter :
      ValuationSubring.idealOfLE R S hRS = IsLocalRing.maximalIdeal R) :
    valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdealStatement R S hRS hcenter := by
  unfold valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdealStatement
  have hcenter_self :
      ValuationSubring.idealOfLE R R le_rfl = IsLocalRing.maximalIdeal R := by
    change (IsLocalRing.maximalIdeal R).comap (R.inclusion R le_rfl) =
      IsLocalRing.maximalIdeal R
    ext x
    rfl
  have hle :
      ValuationSubring.idealOfLE R R le_rfl ≤
        ValuationSubring.idealOfLE R S hRS := by
    intro x hx
    rw [hcenter_self] at hx
    rw [hcenter]
    exact hx
  have hOfPrime :
      ValuationSubring.ofPrime R (ValuationSubring.idealOfLE R S hRS) ≤
        ValuationSubring.ofPrime R (ValuationSubring.idealOfLE R R le_rfl) :=
    ValuationSubring.ofPrime_le_of_le (A := R)
      (ValuationSubring.idealOfLE R R le_rfl)
      (ValuationSubring.idealOfLE R S hRS) hle
  have hSR : S ≤ R := by
    intro x hx
    have hx' :
        x ∈ ValuationSubring.ofPrime R
          (ValuationSubring.idealOfLE R S hRS) := by
      rwa [ValuationSubring.ofPrime_idealOfLE R S hRS]
    have hx'' := hOfPrime hx'
    rwa [ValuationSubring.ofPrime_idealOfLE R R le_rfl] at hx''
  exact le_antisymm hSR hRS

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
