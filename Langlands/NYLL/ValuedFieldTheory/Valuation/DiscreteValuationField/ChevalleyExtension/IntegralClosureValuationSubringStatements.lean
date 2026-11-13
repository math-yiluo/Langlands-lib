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
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.Definitions

/-! Exact proposition targets for the selected NYLL M110 theorem statements. -/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

noncomputable section

universe u v w x y z

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- Proposition target for the pinned source theorem `mem_integralClosureValuationSubringOfMemOrInv`. -/
def mem_integralClosureValuationSubringOfMemOrInvStatement
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)
    (z : L) : Prop :=
    z ∈ integralClosureValuationSubringOfMemOrInv (L := L) vK hval ↔
      z ∈ (integralClosure vK.valuationSubring L).toSubring

/-- Proposition target for the pinned source theorem `integralClosureValuationSubringOfMemOrInv_pullback`. -/
def integralClosureValuationSubringOfMemOrInv_pullbackStatement
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)
    (a : K) : Prop :=
    algebraMap K L a ∈
        integralClosureValuationSubringOfMemOrInv (L := L) vK hval ↔
      a ∈ vK.valuationSubring

/-- Proposition target for the pinned source theorem `integralClosureValuationSubringOfMemOrInv_hasExtension`. -/
def integralClosureValuationSubringOfMemOrInv_hasExtensionStatement
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring) : Prop :=
    vK.HasExtension
      (integralClosureValuationSubringOfMemOrInv (L := L) vK hval).valuation

/-- Proposition target for the pinned source theorem `integralClosureValuationSubringOfMemOrInv_isIntegralClosure`. -/
def integralClosureValuationSubringOfMemOrInv_isIntegralClosureStatement
    (vK : _root_.Valuation K ΓK)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring) : Prop :=
    let B := integralClosureValuationSubringOfMemOrInv (L := L) vK hval
    IsIntegralClosure B vK.valuationSubring L

/-- Proposition target for the pinned source theorem `integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtension`. -/
def integralClosureValuationSubringOfMemOrInv_le_valuationSubring_of_hasExtensionStatement
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    (hval :
      ∀ z : L,
        z ∈ (integralClosure vK.valuationSubring L).toSubring ∨
          z⁻¹ ∈ (integralClosure vK.valuationSubring L).toSubring)
    [vK.HasExtension vL] : Prop :=
    integralClosureValuationSubringOfMemOrInv (L := L) vK hval ≤
      vL.valuationSubring


end

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
