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

/-! Exact proposition targets for the selected NYLL M110 theorem statements. -/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

noncomputable section

universe u v w x y z

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- Proposition target for the pinned source theorem `integralClosure_mem_valuationSubring_of_hasExtension`. -/
def integralClosure_mem_valuationSubring_of_hasExtensionStatement
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] (z : integralClosure vK.valuationSubring L) : Prop :=
    (z : L) ∈ vL.valuationSubring

/-- Proposition target for the pinned source theorem `algebraMap_mem_integralClosure_valuationSubring_iff`. -/
def algebraMap_mem_integralClosure_valuationSubring_iffStatement
    (vK : _root_.Valuation K ΓK) (a : K) : Prop :=
    algebraMap K L a ∈ (integralClosure vK.valuationSubring L).toSubring ↔
      a ∈ vK.valuationSubring

/-- Proposition target for the pinned source theorem `valuationSubring_mem_integralClosure_of_isIntegral`. -/
def valuationSubring_mem_integralClosure_of_isIntegralStatement
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    [Algebra.IsIntegral vK.valuationSubring vL.valuationSubring]
    (z : vL.valuationSubring) : Prop :=
    (z : L) ∈ integralClosure vK.valuationSubring L

/-- Proposition target for the pinned source theorem `valuationSubring_isIntegralClosure_of_isIntegral`. -/
def valuationSubring_isIntegralClosure_of_isIntegralStatement
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL]
    [Algebra.IsIntegral vK.valuationSubring vL.valuationSubring] : Prop :=
    IsIntegralClosure vL.valuationSubring vK.valuationSubring L

/-- Proposition target for the pinned source theorem `valuationSubring_isScalarTower_of_hasExtension`. -/
def valuationSubring_isScalarTower_of_hasExtensionStatement
    {ΓL : Type x} [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    [vK.HasExtension vL] : Prop :=
    IsScalarTower vK.valuationSubring vL.valuationSubring L


end

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
