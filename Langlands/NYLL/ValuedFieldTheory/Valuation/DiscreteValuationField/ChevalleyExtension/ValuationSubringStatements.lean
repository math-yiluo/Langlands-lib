/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modifications by Worker 194 (2026-11-13): extract focused M110 units from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL;
replace upstream imports by focused Mathlib imports and the local definition
module where needed. Retain the source construction and statement telescopes;
convert the selected theorem conclusions to Prop-valued definitions without
publishing their proofs. In M110.013 only, zeta-erase the unused local
HasExtension proof binding in the conclusion. See the paired Markdown for
the exact per-file source correspondence. Retained license and notices:
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.LocalSubring

/-! Exact proposition targets for the selected NYLL M110 theorem statements. -/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

noncomputable section

universe u v w x y z

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- Proposition target for the pinned source theorem `mem_base_valuationSubring_of_lift_mem`. -/
def mem_base_valuationSubring_of_lift_memStatement
    (vK : _root_.Valuation K ΓK)
    (B : ValuationSubring L)
    (hB : ∀ x : vK.valuationSubring, algebraMap vK.valuationSubring L x ∈ B.toSubring)
    (hlocal : IsLocalHom
      ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB))
    {x : K} (hxB : algebraMap K L x ∈ B.toSubring) : Prop :=
    x ∈ vK.valuationSubring

/-- Proposition target for the pinned source theorem `exists_extension_valuationSubring`. -/
def exists_extension_valuationSubringStatement
    (vK : _root_.Valuation K ΓK) : Prop :=
    ∃ B : ValuationSubring L,
      ∃ hB : ∀ x : vK.valuationSubring,
        algebraMap vK.valuationSubring L x ∈ B.toSubring,
        IsLocalHom
          ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB) ∧
        ∀ x : K, algebraMap K L x ∈ B.toSubring ↔
          x ∈ vK.valuationSubring

/-- Proposition target for the pinned source theorem `hasExtension_valuation_of_valuationSubring_pullback`. -/
def hasExtension_valuation_of_valuationSubring_pullbackStatement
    (vK : _root_.Valuation K ΓK) (B : ValuationSubring L)
    (hpullback : ∀ x : K, algebraMap K L x ∈ B.toSubring ↔
      x ∈ vK.valuationSubring) : Prop :=
    vK.HasExtension B.valuation

/-- Proposition target for the pinned source theorem `valuationSubring_pullback_of_hasExtension_valuation`. -/
def valuationSubring_pullback_of_hasExtension_valuationStatement
    (vK : _root_.Valuation K ΓK) (B : ValuationSubring L)
    [vK.HasExtension B.valuation] (x : K) : Prop :=
    algebraMap K L x ∈ B.toSubring ↔ x ∈ vK.valuationSubring

/-- Proposition target for the pinned source theorem `valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdeal`. -/
def valuationSubring_eq_of_le_of_idealOfLE_eq_maximalIdealStatement
    (R S : ValuationSubring L) (hRS : R ≤ S)
    (hcenter :
      ValuationSubring.idealOfLE R S hRS = IsLocalRing.maximalIdeal R) : Prop :=
    S = R


end

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
