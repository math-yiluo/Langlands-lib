/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299, 2026-11-14: prove the exact M363.003 target from
NYLL at commit fbd320cd8b1b06487c58227e92eb135794267709 in the
Langlands.NYLL namespace. Replace the product of graded pieces by the
third isomorphism theorem and the published whole-parameter cardinality.
See the paired Markdown for the source correspondence and modifications.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration.CardinalityStatement
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.CardinalityProof

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF

variable {K : Type u} [Field K]

theorem standardLubinTateUnitParameterSubgroup_natCard
    (F : LocalField.{u, v} K) {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    standardLubinTateUnitParameterSubgroup_natCardStatement F hπ n k hk hkn := by
  let H := standardLubinTateUnitParameterSubgroup F n k
  let q := Nat.card F.residueField
  have hle : higherPrincipalUnitGroup F.toCompleteDVF (n + 1) ≤
      higherPrincipalUnitGroup F.toCompleteDVF k := by
    intro a ha
    exact (Ideal.pow_le_pow_right hkn) ha
  have hidx : H.index = (q - 1) * q ^ (k - 1) := by
    change Nat.card (standardLubinTateUnitParameter F n ⧸ H) = _
    calc
      _ = Nat.card (F.valuationSubringˣ ⧸
          higherPrincipalUnitGroup F.toCompleteDVF k) :=
        Nat.card_congr (QuotientGroup.quotientQuotientEquivQuotient
          (higherPrincipalUnitGroup F.toCompleteDVF (n + 1))
          (higherPrincipalUnitGroup F.toCompleteDVF k) hle).toEquiv
      _ = (q - 1) * q ^ (k - 1) := by
        have h := standardLubinTateUnitParameter_natCard F (k - 1)
        have hk' : k - 1 + 1 = k := by omega
        change Nat.card (F.valuationSubringˣ ⧸
          higherPrincipalUnitGroup F.toCompleteDVF (k - 1 + 1)) =
            (q - 1) * q ^ (k - 1) at h
        rwa [hk'] at h
  have hfull := standardLubinTateUnitParameter_natCard F n
  change Nat.card (standardLubinTateUnitParameter F n) = (q - 1) * q ^ n at hfull
  have hmul := H.card_mul_index
  rw [hidx, hfull] at hmul
  have hpos : 0 < (q - 1) * q ^ (k - 1) :=
    Nat.mul_pos (Nat.sub_pos_of_lt Finite.one_lt_card) (pow_pos Nat.card_pos _)
  have hexp : n + 1 - k + (k - 1) = n := by omega
  have hpow : q ^ (n + 1 - k) * q ^ (k - 1) = q ^ n := by
    rw [← pow_add, hexp]
  change Nat.card H = q ^ (n + 1 - k)
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    Nat.card H * ((q - 1) * q ^ (k - 1)) = (q - 1) * q ^ n := hmul
    _ = (q - 1) * (q ^ (n + 1 - k) * q ^ (k - 1)) := by rw [hpow]
    _ = q ^ (n + 1 - k) * ((q - 1) * q ^ (k - 1)) := by ac_rfl

end Langlands.NYLL.LubinTate
